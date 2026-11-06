import NetHack.Soko22Hazard87.AndIntroBlocks0017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro4500 (p : Pattern) (ha : d1436 p = 1) (hb : d70145 p = 1) : d6378 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1424 q = 1) : d1424 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1433 q = 1) (hb : d70145 q = 1) : d6375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d70145, d6375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1433, d70145, d6375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1434 q = 1) (hb : d70145 q = 1) : d6376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d6376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1434, d6376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1435 q = 1) (hb : d70145 q = 1) : d6377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d6377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1435, d6377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1436 q = 1) (hb : d70145 q = 1) : d6378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d6378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1436, d6378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro4501 (p : Pattern) (ha : d4509 p = 1) (hb : d70147 p = 1) : d71748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1437 q = 1) (hb : d70147 q = 1) : d71743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d70147, d71743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1437, d70147, d71743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4500 q ha hb
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d70147 q = 1) : d71744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d71744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4505, d71744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1436 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1487 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d1487, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1488 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4506 q = 1) (hb : d70147 q = 1) : d71745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d71745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4506, d71745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4507 q = 1) (hb : d70147 q = 1) : d71746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d71746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d71746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4508 q = 1) (hb : d70147 q = 1) : d71747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d71747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d71747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4509 q = 1) (hb : d70147 q = 1) : d71748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d71748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d71748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4502 (p : Pattern) (ha : d1158 p = 1) (hb : d70145 p = 1) : d6257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1150 q = 1) : d1150 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1155 q = 1) (hb : d70145 q = 1) : d6254 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d70145, d6254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1155, d70145, d6254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1156 q = 1) (hb : d70145 q = 1) : d6255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d6255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1156, d6255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1157 q = 1) (hb : d70145 q = 1) : d6256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d6256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1157, d6256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1158 q = 1) (hb : d70145 q = 1) : d6257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d6257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d6257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4503 (p : Pattern) (ha : d51738 p = 1) (hb : d70147 p = 1) : d71717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1185 q = 1) (hb : d70145 q = 1) : d1185 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1186 q = 1) (hb : d70147 q = 1) : d71705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d70147, d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1186, d70147, d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1187 q = 1) (hb : d70147 q = 1) : d71706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d70147 q = 1) : d71707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1188, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d70147 q = 1) : d71708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1192 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1195 q = 1) (hb : d70145 q = 1) : d1195 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1196 q = 1) (hb : d70147 q = 1) : d71709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d70147, d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1196, d70147, d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1197 q = 1) (hb : d70147 q = 1) : d71710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1198 q = 1) (hb : d70147 q = 1) : d71711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1198, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1227 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1228 q = 1) (hb : d70147 q = 1) : d71712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d70147, d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1228, d70147, d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4502 q ha hb
  have h14 (q : Pattern) (ha : d4485 q = 1) (hb : d70147 q = 1) : d71713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4485, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1320 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1320, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1321 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4486 q = 1) (hb : d70147 q = 1) : d71714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4486, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51736 q = 1) (hb : d70147 q = 1) : d71715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51736, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51737 q = 1) (hb : d70147 q = 1) : d71716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51737, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51738 q = 1) (hb : d70147 q = 1) : d71717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d71717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d71717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4504 (p : Pattern) (ha : d51741 p = 1) (hb : d70147 p = 1) : d71730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1185 q = 1) (hb : d70145 q = 1) : d1185 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1186 q = 1) (hb : d70147 q = 1) : d71705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d70147, d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1186, d70147, d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1187 q = 1) (hb : d70147 q = 1) : d71706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d70147 q = 1) : d71707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1188, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d70147 q = 1) : d71708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1192 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1195 q = 1) (hb : d70145 q = 1) : d1195 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1196 q = 1) (hb : d70147 q = 1) : d71709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d70147, d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1196, d70147, d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1197 q = 1) (hb : d70147 q = 1) : d71710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1198 q = 1) (hb : d70147 q = 1) : d71711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1198, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1227 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1228 q = 1) (hb : d70147 q = 1) : d71712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d70147, d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1228, d70147, d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4502 q ha hb
  have h14 (q : Pattern) (ha : d4485 q = 1) (hb : d70147 q = 1) : d71713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4485, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1320 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1320, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1321 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4486 q = 1) (hb : d70147 q = 1) : d71714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4486, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51736 q = 1) (hb : d70147 q = 1) : d71715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51736, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51737 q = 1) (hb : d70147 q = 1) : d71716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51737, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d1326 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d1327 q = 1) (hb : d70145 q = 1) : d1327 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d1328 q = 1) (hb : d70147 q = 1) : d71718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d70147, d71718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d1328, d70147, d71718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1329 q = 1) (hb : d70147 q = 1) : d71719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d71719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d71719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1330 q = 1) (hb : d70147 q = 1) : d71720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d71720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d1330, d71720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d1331 q = 1) (hb : d70147 q = 1) : d71721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d71721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d71721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d1332 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d1333 q = 1) (hb : d70145 q = 1) : d1333 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d1334 q = 1) (hb : d70147 q = 1) : d71722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d70147, d71722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
    | true =>
      simp only [d1334, d70147, d71722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d1335 q = 1) (hb : d70147 q = 1) : d71723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d71723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d71723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d1336 q = 1) (hb : d70147 q = 1) : d71724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d71724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d1336, d71724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d0 q = 1) (hb : d1337 q = 1) : d0 q = 1 := by
    exact ha
  have h34 (q : Pattern) (ha : d1338 q = 1) (hb : d70147 q = 1) : d71725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d70147, d71725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q hb ha
    | true =>
      simp only [d1338, d70147, d71725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4498 q ha hb
  have h35 (q : Pattern) (ha : d4490 q = 1) (hb : d70147 q = 1) : d71726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d71726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4490, d71726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h36 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h37 (q : Pattern) (ha : d1343 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q hb ha
    | true =>
      simp only [d1343, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h38 (q : Pattern) (ha : d1344 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
    | true =>
      simp only [d1344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h39 (q : Pattern) (ha : d4491 q = 1) (hb : d70147 q = 1) : d71727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d71727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
    | true =>
      simp only [d4491, d71727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  have h40 (q : Pattern) (ha : d51739 q = 1) (hb : d70147 q = 1) : d71728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d71728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51739, d71728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h39 q ha hb
  have h41 (q : Pattern) (ha : d51740 q = 1) (hb : d70147 q = 1) : d71729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d71729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d51740, d71729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h40 q ha hb
  have h42 (q : Pattern) (ha : d51741 q = 1) (hb : d70147 q = 1) : d71730 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d71730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51741, d71730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h41 q ha hb
  exact h42 p ha hb
theorem andIntro4505 (p : Pattern) (ha : d58660 p = 1) (hb : d70148 p = 1) : d71754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d70147 q = 1) : d71694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d71694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d71694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4496 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1170 q = 1) (hb : d70148 q = 1) : d71695 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d70148, d71695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d70148, d71695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1179 q = 1) (hb : d70147 q = 1) : d71702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4496 q ha hb
    | true =>
      simp only [d1179, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4497 q ha hb
  have h5 (q : Pattern) (ha : d1180 q = 1) (hb : d70148 q = 1) : d71703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d70148, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1180, d70148, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1181 q = 1) (hb : d70148 q = 1) : d71704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d71704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1181, d71704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51742 q = 1) (hb : d70147 q = 1) : d71731 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d71731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4503 q ha hb
    | true =>
      simp only [d51742, d71731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4504 q ha hb
  have h8 (q : Pattern) (ha : d58656 q = 1) (hb : d70148 q = 1) : d71732 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58656, d70148, d71732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58656, d70148, d71732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58657 q = 1) (hb : d70148 q = 1) : d71733 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58657, d71733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58657, d71733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58658 q = 1) (hb : d70148 q = 1) : d71734 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58658, d71734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58658, d71734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4500 q = 1) (hb : d70147 q = 1) : d71738 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d71738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d71738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4499 q ha hb
  have h13 (q : Pattern) (ha : d4501 q = 1) (hb : d70148 q = 1) : d71739 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d70148, d71739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4501, d70148, d71739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4502 q = 1) (hb : d70148 q = 1) : d71740 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d71740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4502, d71740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4503 q = 1) (hb : d70148 q = 1) : d71741 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d71741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4503, d71741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58659 q = 1) (hb : d70148 q = 1) : d71742 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58659, d71742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58659, d71742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4510 q = 1) (hb : d70147 q = 1) : d71749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d71749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d71749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4501 q ha hb
  have h18 (q : Pattern) (ha : d4511 q = 1) (hb : d70148 q = 1) : d71750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d70148, d71750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4511, d70148, d71750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4512 q = 1) (hb : d70148 q = 1) : d71751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d71751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4512, d71751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4513 q = 1) (hb : d70148 q = 1) : d71752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d71752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4513, d71752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4514 q = 1) (hb : d70148 q = 1) : d71753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d71753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4514, d71753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58660 q = 1) (hb : d70148 q = 1) : d71754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d71754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58660, d71754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4506 (p : Pattern) (ha : d58666 p = 1) (hb : d70148 p = 1) : d71760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d70148 q = 1) : d71755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d71755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d71755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4505 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d70148 q = 1) : d71756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d71756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d71756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d70148 q = 1) : d71757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d71757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d71757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d70148 q = 1) : d71758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d71758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d71758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d70148 q = 1) : d71759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d71759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d71759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d70148 q = 1) : d71760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d71760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d71760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4507 (p : Pattern) (ha : d1629 p = 1) (hb : d70147 p = 1) : d71769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1623 q = 1) (hb : d70145 q = 1) : d1623 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d70147 q = 1) : d71764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d70147, d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1624, d70147, d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d70147 q = 1) : d71765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d70147 q = 1) : d71766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d70147 q = 1) : d71767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d70147 q = 1) : d71768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1629 q = 1) (hb : d70147 q = 1) : d71769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d71769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d71769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4508 (p : Pattern) (ha : d1639 p = 1) (hb : d70147 p = 1) : d71777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1623 q = 1) (hb : d70145 q = 1) : d1623 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d70147 q = 1) : d71764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d70147, d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1624, d70147, d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d70147 q = 1) : d71765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d70147 q = 1) : d71766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d70147 q = 1) : d71767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d70147 q = 1) : d71768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1633 q = 1) (hb : d70145 q = 1) : d1633 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1634 q = 1) (hb : d70147 q = 1) : d71772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d70147, d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1634, d70147, d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1635 q = 1) (hb : d70147 q = 1) : d71773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1636 q = 1) (hb : d70147 q = 1) : d71774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1636, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1637 q = 1) (hb : d70147 q = 1) : d71775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1638 q = 1) (hb : d70147 q = 1) : d71776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1639 q = 1) (hb : d70147 q = 1) : d71777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1639, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4509 (p : Pattern) (ha : d1632 p = 1) (hb : d70145 p = 1) : d6412 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1611 q = 1) : d1611 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1616 q = 1) (hb : d70145 q = 1) : d6400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d70145, d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1616, d70145, d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1617 q = 1) (hb : d70145 q = 1) : d6401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d6401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1617, d6401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1618 q = 1) (hb : d70145 q = 1) : d6402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d6402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1618, d6402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1632 q = 1) (hb : d70145 q = 1) : d6412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d6412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1632, d6412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro4510 (p : Pattern) (ha : d4539 p = 1) (hb : d70147 p = 1) : d71813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1815 q = 1) (hb : d70147 q = 1) : d71801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d70147, d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1815, d70147, d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d70147 q = 1) : d71802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4530, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1820 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d1820, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1821 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4531 q = 1) (hb : d70147 q = 1) : d71803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4531, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4532 q = 1) (hb : d70147 q = 1) : d71811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d71811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d71811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4533 q = 1) (hb : d70147 q = 1) : d71812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d71812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d71812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4539 q = 1) (hb : d70147 q = 1) : d71813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d71813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d71813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4511 (p : Pattern) (ha : d1913 p = 1) (hb : d70145 p = 1) : d6524 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1901 q = 1) : d1901 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1910 q = 1) (hb : d70145 q = 1) : d6521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d70145, d6521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1910, d70145, d6521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1911 q = 1) (hb : d70145 q = 1) : d6522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d6522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1911, d6522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1912 q = 1) (hb : d70145 q = 1) : d6523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d6523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1912, d6523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1913 q = 1) (hb : d70145 q = 1) : d6524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d6524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1913, d6524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro4512 (p : Pattern) (ha : d4549 p = 1) (hb : d70147 p = 1) : d71824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1914 q = 1) (hb : d70147 q = 1) : d71819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d70147, d71819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1914, d70147, d71819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4511 q ha hb
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d70147 q = 1) : d71820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d71820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4545, d71820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1964 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d1964, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1965 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4546 q = 1) (hb : d70147 q = 1) : d71821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d71821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4546, d71821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4547 q = 1) (hb : d70147 q = 1) : d71822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d71822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d71822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4548 q = 1) (hb : d70147 q = 1) : d71823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d71823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d71823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4549 q = 1) (hb : d70147 q = 1) : d71824 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d71824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d71824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4513 (p : Pattern) (ha : d1619 p = 1) (hb : d70145 p = 1) : d6403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1611 q = 1) : d1611 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1616 q = 1) (hb : d70145 q = 1) : d6400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d70145, d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1616, d70145, d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1617 q = 1) (hb : d70145 q = 1) : d6401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d6401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1617, d6401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1618 q = 1) (hb : d70145 q = 1) : d6402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d6402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1618, d6402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1619 q = 1) (hb : d70145 q = 1) : d6403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d6403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d6403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4514 (p : Pattern) (ha : d51766 p = 1) (hb : d70147 p = 1) : d71793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1646 q = 1) (hb : d70145 q = 1) : d1646 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1647 q = 1) (hb : d70147 q = 1) : d71781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d70147, d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1647, d70147, d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1648 q = 1) (hb : d70147 q = 1) : d71782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d70147 q = 1) : d71783 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1649, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d70147 q = 1) : d71784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1653 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1656 q = 1) (hb : d70145 q = 1) : d1656 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1657 q = 1) (hb : d70147 q = 1) : d71785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d70147, d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1657, d70147, d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1658 q = 1) (hb : d70147 q = 1) : d71786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1659 q = 1) (hb : d70147 q = 1) : d71787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1659, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1682 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1683 q = 1) (hb : d70147 q = 1) : d71788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d70147, d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1683, d70147, d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4513 q ha hb
  have h14 (q : Pattern) (ha : d4525 q = 1) (hb : d70147 q = 1) : d71789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4525, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1797 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1797, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1798 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4526 q = 1) (hb : d70147 q = 1) : d71790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4526, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51764 q = 1) (hb : d70147 q = 1) : d71791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51764, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51765 q = 1) (hb : d70147 q = 1) : d71792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51765, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51766 q = 1) (hb : d70147 q = 1) : d71793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d71793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d71793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4515 (p : Pattern) (ha : d51769 p = 1) (hb : d70147 p = 1) : d71806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1646 q = 1) (hb : d70145 q = 1) : d1646 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1647 q = 1) (hb : d70147 q = 1) : d71781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d70147, d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1647, d70147, d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1648 q = 1) (hb : d70147 q = 1) : d71782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d70147 q = 1) : d71783 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1649, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d70147 q = 1) : d71784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1653 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1656 q = 1) (hb : d70145 q = 1) : d1656 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1657 q = 1) (hb : d70147 q = 1) : d71785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d70147, d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1657, d70147, d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1658 q = 1) (hb : d70147 q = 1) : d71786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1659 q = 1) (hb : d70147 q = 1) : d71787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1659, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1682 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1683 q = 1) (hb : d70147 q = 1) : d71788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d70147, d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1683, d70147, d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4513 q ha hb
  have h14 (q : Pattern) (ha : d4525 q = 1) (hb : d70147 q = 1) : d71789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4525, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1797 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1797, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1798 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4526 q = 1) (hb : d70147 q = 1) : d71790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4526, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51764 q = 1) (hb : d70147 q = 1) : d71791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51764, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51765 q = 1) (hb : d70147 q = 1) : d71792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51765, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d1803 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d1804 q = 1) (hb : d70145 q = 1) : d1804 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d1805 q = 1) (hb : d70147 q = 1) : d71794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d70147, d71794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d1805, d70147, d71794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1806 q = 1) (hb : d70147 q = 1) : d71795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d71795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d71795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1807 q = 1) (hb : d70147 q = 1) : d71796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d71796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d1807, d71796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d1808 q = 1) (hb : d70147 q = 1) : d71797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d71797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d71797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d1809 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d1810 q = 1) (hb : d70145 q = 1) : d1810 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d1811 q = 1) (hb : d70147 q = 1) : d71798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d70147, d71798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
    | true =>
      simp only [d1811, d70147, d71798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d1812 q = 1) (hb : d70147 q = 1) : d71799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d71799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d71799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d1813 q = 1) (hb : d70147 q = 1) : d71800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d71800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d1813, d71800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d0 q = 1) (hb : d1814 q = 1) : d0 q = 1 := by
    exact ha
  have h34 (q : Pattern) (ha : d1815 q = 1) (hb : d70147 q = 1) : d71801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d70147, d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q hb ha
    | true =>
      simp only [d1815, d70147, d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
  have h35 (q : Pattern) (ha : d4530 q = 1) (hb : d70147 q = 1) : d71802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4530, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h36 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h37 (q : Pattern) (ha : d1820 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q hb ha
    | true =>
      simp only [d1820, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h38 (q : Pattern) (ha : d1821 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
    | true =>
      simp only [d1821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h39 (q : Pattern) (ha : d4531 q = 1) (hb : d70147 q = 1) : d71803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
    | true =>
      simp only [d4531, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  have h40 (q : Pattern) (ha : d51767 q = 1) (hb : d70147 q = 1) : d71804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d71804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51767, d71804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h39 q ha hb
  have h41 (q : Pattern) (ha : d51768 q = 1) (hb : d70147 q = 1) : d71805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d71805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d51768, d71805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h40 q ha hb
  have h42 (q : Pattern) (ha : d51769 q = 1) (hb : d70147 q = 1) : d71806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d71806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51769, d71806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h41 q ha hb
  exact h42 p ha hb
theorem andIntro4516 (p : Pattern) (ha : d58674 p = 1) (hb : d70148 p = 1) : d71830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d70147 q = 1) : d71770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d71770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d71770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4507 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1631 q = 1) (hb : d70148 q = 1) : d71771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d70148, d71771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d70148, d71771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1640 q = 1) (hb : d70147 q = 1) : d71778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4507 q ha hb
    | true =>
      simp only [d1640, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4508 q ha hb
  have h5 (q : Pattern) (ha : d1641 q = 1) (hb : d70148 q = 1) : d71779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d70148, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1641, d70148, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1642 q = 1) (hb : d70148 q = 1) : d71780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d71780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1642, d71780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51770 q = 1) (hb : d70147 q = 1) : d71807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d71807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4514 q ha hb
    | true =>
      simp only [d51770, d71807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4515 q ha hb
  have h8 (q : Pattern) (ha : d58670 q = 1) (hb : d70148 q = 1) : d71808 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58670, d70148, d71808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58670, d70148, d71808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58671 q = 1) (hb : d70148 q = 1) : d71809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58671, d71809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58671, d71809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58672 q = 1) (hb : d70148 q = 1) : d71810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58672, d71810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58672, d71810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4540 q = 1) (hb : d70147 q = 1) : d71814 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d71814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d71814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4510 q ha hb
  have h13 (q : Pattern) (ha : d4541 q = 1) (hb : d70148 q = 1) : d71815 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d70148, d71815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4541, d70148, d71815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4542 q = 1) (hb : d70148 q = 1) : d71816 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d71816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4542, d71816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4543 q = 1) (hb : d70148 q = 1) : d71817 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d71817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4543, d71817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58673 q = 1) (hb : d70148 q = 1) : d71818 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58673, d71818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58673, d71818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4550 q = 1) (hb : d70147 q = 1) : d71825 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d71825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d71825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4512 q ha hb
  have h18 (q : Pattern) (ha : d4551 q = 1) (hb : d70148 q = 1) : d71826 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d70148, d71826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4551, d70148, d71826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4552 q = 1) (hb : d70148 q = 1) : d71827 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d71827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4552, d71827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4553 q = 1) (hb : d70148 q = 1) : d71828 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d71828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4553, d71828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4554 q = 1) (hb : d70148 q = 1) : d71829 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d71829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4554, d71829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58674 q = 1) (hb : d70148 q = 1) : d71830 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d71830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58674, d71830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4517 (p : Pattern) (ha : d58680 p = 1) (hb : d70148 p = 1) : d71836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d70148 q = 1) : d71831 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d71831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d71831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4516 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d70148 q = 1) : d71832 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d71832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d71832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d70148 q = 1) : d71833 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d71833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d71833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d70148 q = 1) : d71834 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d71834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d71834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d70148 q = 1) : d71835 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d71835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d71835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d70148 q = 1) : d71836 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d71836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d71836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4518 (p : Pattern) (ha : d2112 p = 1) (hb : d70147 p = 1) : d71846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2106 q = 1) (hb : d70145 q = 1) : d2106 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d70147 q = 1) : d71841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d70147, d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2107, d70147, d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d70147 q = 1) : d71842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d70147 q = 1) : d71843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d70147 q = 1) : d71844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d70147 q = 1) : d71845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2112 q = 1) (hb : d70147 q = 1) : d71846 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d71846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d71846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4519 (p : Pattern) (ha : d2122 p = 1) (hb : d70147 p = 1) : d71854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2106 q = 1) (hb : d70145 q = 1) : d2106 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d70147 q = 1) : d71841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d70147, d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2107, d70147, d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d70147 q = 1) : d71842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d70147 q = 1) : d71843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d70147 q = 1) : d71844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d70147 q = 1) : d71845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2116 q = 1) (hb : d70145 q = 1) : d2116 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2117 q = 1) (hb : d70147 q = 1) : d71849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d70147, d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d2117, d70147, d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2118 q = 1) (hb : d70147 q = 1) : d71850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2119 q = 1) (hb : d70147 q = 1) : d71851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2119, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2120 q = 1) (hb : d70147 q = 1) : d71852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2121 q = 1) (hb : d70147 q = 1) : d71853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2122 q = 1) (hb : d70147 q = 1) : d71854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2122, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4520 (p : Pattern) (ha : d2115 p = 1) (hb : d70145 p = 1) : d6559 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2094 q = 1) : d2094 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2099 q = 1) (hb : d70145 q = 1) : d6547 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d70145, d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2099, d70145, d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2100 q = 1) (hb : d70145 q = 1) : d6548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d6548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2100, d6548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2101 q = 1) (hb : d70145 q = 1) : d6549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d6549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2101, d6549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2115 q = 1) (hb : d70145 q = 1) : d6559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, d6559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2115, d6559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro4521 (p : Pattern) (ha : d4580 p = 1) (hb : d70147 p = 1) : d71890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2293 q = 1) (hb : d70147 q = 1) : d71878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d70147, d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2293, d70147, d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4520 q ha hb
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d70147 q = 1) : d71879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4571, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2298 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d2298, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2299 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4572 q = 1) (hb : d70147 q = 1) : d71880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4572, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4573 q = 1) (hb : d70147 q = 1) : d71888 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d71888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d71888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4574 q = 1) (hb : d70147 q = 1) : d71889 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d71889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d71889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4580 q = 1) (hb : d70147 q = 1) : d71890 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d71890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d71890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4522 (p : Pattern) (ha : d2391 p = 1) (hb : d70145 p = 1) : d6671 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2379 q = 1) : d2379 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2388 q = 1) (hb : d70145 q = 1) : d6668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d70145, d6668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2388, d70145, d6668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2389 q = 1) (hb : d70145 q = 1) : d6669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d6669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2389, d6669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2390 q = 1) (hb : d70145 q = 1) : d6670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d6670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2390, d6670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2391 q = 1) (hb : d70145 q = 1) : d6671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d6671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2391, d6671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro4523 (p : Pattern) (ha : d4590 p = 1) (hb : d70147 p = 1) : d71901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2383 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2392 q = 1) (hb : d70147 q = 1) : d71896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d70147, d71896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2392, d70147, d71896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4522 q ha hb
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d70147 q = 1) : d71897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d71897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4586, d71897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2391 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2442 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d2442, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2443 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4587 q = 1) (hb : d70147 q = 1) : d71898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d71898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4587, d71898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4588 q = 1) (hb : d70147 q = 1) : d71899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d71899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d71899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4589 q = 1) (hb : d70147 q = 1) : d71900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d71900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d71900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4590 q = 1) (hb : d70147 q = 1) : d71901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d71901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d71901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4524 (p : Pattern) (ha : d2102 p = 1) (hb : d70145 p = 1) : d6550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2094 q = 1) : d2094 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2099 q = 1) (hb : d70145 q = 1) : d6547 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d70145, d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2099, d70145, d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2100 q = 1) (hb : d70145 q = 1) : d6548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d6548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2100, d6548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2101 q = 1) (hb : d70145 q = 1) : d6549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d6549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2101, d6549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2102 q = 1) (hb : d70145 q = 1) : d6550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d6550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d6550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4525 (p : Pattern) (ha : d51795 p = 1) (hb : d70147 p = 1) : d71870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2129 q = 1) (hb : d70145 q = 1) : d2129 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2130 q = 1) (hb : d70147 q = 1) : d71858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d70147, d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2130, d70147, d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2131 q = 1) (hb : d70147 q = 1) : d71859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d70147 q = 1) : d71860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2132, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d70147 q = 1) : d71861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2136 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2139 q = 1) (hb : d70145 q = 1) : d2139 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2140 q = 1) (hb : d70147 q = 1) : d71862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d70147, d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2140, d70147, d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2141 q = 1) (hb : d70147 q = 1) : d71863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2142 q = 1) (hb : d70147 q = 1) : d71864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2142, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d2161 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2162 q = 1) (hb : d70147 q = 1) : d71865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d70147, d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2162, d70147, d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4524 q ha hb
  have h14 (q : Pattern) (ha : d4566 q = 1) (hb : d70147 q = 1) : d71866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4566, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d2275 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d2275, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2276 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4567 q = 1) (hb : d70147 q = 1) : d71867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4567, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51793 q = 1) (hb : d70147 q = 1) : d71868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51793, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51794 q = 1) (hb : d70147 q = 1) : d71869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51794, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d51795 q = 1) (hb : d70147 q = 1) : d71870 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d71870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d71870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4526 (p : Pattern) (ha : d51798 p = 1) (hb : d70147 p = 1) : d71883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2129 q = 1) (hb : d70145 q = 1) : d2129 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2130 q = 1) (hb : d70147 q = 1) : d71858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d70147, d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2130, d70147, d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2131 q = 1) (hb : d70147 q = 1) : d71859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d70147 q = 1) : d71860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2132, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d70147 q = 1) : d71861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2136 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2139 q = 1) (hb : d70145 q = 1) : d2139 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2140 q = 1) (hb : d70147 q = 1) : d71862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d70147, d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2140, d70147, d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2141 q = 1) (hb : d70147 q = 1) : d71863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2142 q = 1) (hb : d70147 q = 1) : d71864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2142, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d2161 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2162 q = 1) (hb : d70147 q = 1) : d71865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d70147, d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2162, d70147, d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4524 q ha hb
  have h14 (q : Pattern) (ha : d4566 q = 1) (hb : d70147 q = 1) : d71866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4566, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d2275 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d2275, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2276 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4567 q = 1) (hb : d70147 q = 1) : d71867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4567, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51793 q = 1) (hb : d70147 q = 1) : d71868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51793, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51794 q = 1) (hb : d70147 q = 1) : d71869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51794, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d2281 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d2282 q = 1) (hb : d70145 q = 1) : d2282 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d2283 q = 1) (hb : d70147 q = 1) : d71871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d70147, d71871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d2283, d70147, d71871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d2284 q = 1) (hb : d70147 q = 1) : d71872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d71872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d71872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d2285 q = 1) (hb : d70147 q = 1) : d71873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d71873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d2285, d71873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d2286 q = 1) (hb : d70147 q = 1) : d71874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d71874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d71874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d2287 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d2288 q = 1) (hb : d70145 q = 1) : d2288 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d2289 q = 1) (hb : d70147 q = 1) : d71875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d70147, d71875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
    | true =>
      simp only [d2289, d70147, d71875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d2290 q = 1) (hb : d70147 q = 1) : d71876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d71876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d71876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d2291 q = 1) (hb : d70147 q = 1) : d71877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d71877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d2291, d71877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d0 q = 1) (hb : d2292 q = 1) : d0 q = 1 := by
    exact ha
  have h34 (q : Pattern) (ha : d2293 q = 1) (hb : d70147 q = 1) : d71878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d70147, d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q hb ha
    | true =>
      simp only [d2293, d70147, d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4520 q ha hb
  have h35 (q : Pattern) (ha : d4571 q = 1) (hb : d70147 q = 1) : d71879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4571, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h36 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h37 (q : Pattern) (ha : d2298 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q hb ha
    | true =>
      simp only [d2298, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h38 (q : Pattern) (ha : d2299 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
    | true =>
      simp only [d2299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h39 (q : Pattern) (ha : d4572 q = 1) (hb : d70147 q = 1) : d71880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
    | true =>
      simp only [d4572, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  have h40 (q : Pattern) (ha : d51796 q = 1) (hb : d70147 q = 1) : d71881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d71881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51796, d71881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h39 q ha hb
  have h41 (q : Pattern) (ha : d51797 q = 1) (hb : d70147 q = 1) : d71882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d71882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d51797, d71882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h40 q ha hb
  have h42 (q : Pattern) (ha : d51798 q = 1) (hb : d70147 q = 1) : d71883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d71883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51798, d71883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h41 q ha hb
  exact h42 p ha hb
theorem andIntro4527 (p : Pattern) (ha : d58689 p = 1) (hb : d70148 p = 1) : d71907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d70147 q = 1) : d71847 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d71847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d71847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4518 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2114 q = 1) (hb : d70148 q = 1) : d71848 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d70148, d71848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d70148, d71848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2123 q = 1) (hb : d70147 q = 1) : d71855 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4518 q ha hb
    | true =>
      simp only [d2123, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4519 q ha hb
  have h5 (q : Pattern) (ha : d2124 q = 1) (hb : d70148 q = 1) : d71856 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d70148, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2124, d70148, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d2125 q = 1) (hb : d70148 q = 1) : d71857 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d71857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2125, d71857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51799 q = 1) (hb : d70147 q = 1) : d71884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d71884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4525 q ha hb
    | true =>
      simp only [d51799, d71884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4526 q ha hb
  have h8 (q : Pattern) (ha : d58685 q = 1) (hb : d70148 q = 1) : d71885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58685, d70148, d71885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58685, d70148, d71885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58686 q = 1) (hb : d70148 q = 1) : d71886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58686, d71886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58686, d71886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58687 q = 1) (hb : d70148 q = 1) : d71887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58687, d71887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58687, d71887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4581 q = 1) (hb : d70147 q = 1) : d71891 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d71891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d71891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4521 q ha hb
  have h13 (q : Pattern) (ha : d4582 q = 1) (hb : d70148 q = 1) : d71892 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d70148, d71892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4582, d70148, d71892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4583 q = 1) (hb : d70148 q = 1) : d71893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d71893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4583, d71893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4584 q = 1) (hb : d70148 q = 1) : d71894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d71894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4584, d71894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58688 q = 1) (hb : d70148 q = 1) : d71895 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58688, d71895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58688, d71895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4591 q = 1) (hb : d70147 q = 1) : d71902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d71902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d71902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4523 q ha hb
  have h18 (q : Pattern) (ha : d4592 q = 1) (hb : d70148 q = 1) : d71903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d70148, d71903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4592, d70148, d71903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4593 q = 1) (hb : d70148 q = 1) : d71904 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d71904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4593, d71904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4594 q = 1) (hb : d70148 q = 1) : d71905 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d71905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4594, d71905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4595 q = 1) (hb : d70148 q = 1) : d71906 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d71906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4595, d71906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58689 q = 1) (hb : d70148 q = 1) : d71907 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58689, d71907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58689, d71907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4528 (p : Pattern) (ha : d58695 p = 1) (hb : d70148 p = 1) : d71913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58690 q = 1) (hb : d70148 q = 1) : d71908 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58690, d71908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58690, d71908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4527 q ha hb
  have h2 (q : Pattern) (ha : d58691 q = 1) (hb : d70148 q = 1) : d71909 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58691, d71909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58691, d71909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58692 q = 1) (hb : d70148 q = 1) : d71910 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58692, d71910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58692, d71910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58693 q = 1) (hb : d70148 q = 1) : d71911 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58693, d71911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58693, d71911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58694 q = 1) (hb : d70148 q = 1) : d71912 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58694, d71912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58694, d71912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58695 q = 1) (hb : d70148 q = 1) : d71913 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58695, d71913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58695, d71913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4529 (p : Pattern) (ha : d58701 p = 1) (hb : d70148 p = 1) : d71919 p = 1 := by
  have h0 (q : Pattern) (ha : d58642 q = 1) (hb : d70148 q = 1) : d71612 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58642, d71612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4473 q ha hb
    | true =>
      simp only [d58642, d71612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4484 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58654 q = 1) (hb : d70148 q = 1) : d71686 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58654, d71686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58654, d71686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4495 q ha hb
  have h3 (q : Pattern) (ha : d58655 q = 1) (hb : d70148 q = 1) : d71687 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58655, d71687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58655, d71687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58667 q = 1) (hb : d70148 q = 1) : d71761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58667, d71761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58667, d71761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4506 q ha hb
  have h5 (q : Pattern) (ha : d58668 q = 1) (hb : d70148 q = 1) : d71762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58668, d71762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58668, d71762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58669 q = 1) (hb : d70148 q = 1) : d71763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58669, d71763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58669, d71763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58681 q = 1) (hb : d70148 q = 1) : d71837 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58681, d71837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58681, d71837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4517 q ha hb
  have h8 (q : Pattern) (ha : d58682 q = 1) (hb : d70148 q = 1) : d71838 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58682, d71838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58682, d71838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58683 q = 1) (hb : d70148 q = 1) : d71839 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58683, d71839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58683, d71839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58684 q = 1) (hb : d70148 q = 1) : d71840 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58684, d71840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58684, d71840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58696 q = 1) (hb : d70148 q = 1) : d71914 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58696, d71914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58696, d71914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4528 q ha hb
  have h12 (q : Pattern) (ha : d58697 q = 1) (hb : d70148 q = 1) : d71915 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58697, d71915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58697, d71915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58698 q = 1) (hb : d70148 q = 1) : d71916 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58698, d71916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58698, d71916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58699 q = 1) (hb : d70148 q = 1) : d71917 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58699, d71917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58699, d71917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58700 q = 1) (hb : d70148 q = 1) : d71918 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58700, d71918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58700, d71918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58701 q = 1) (hb : d70148 q = 1) : d71919 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58701, d71919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58701, d71919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4530 (p : Pattern) (ha : d58707 p = 1) (hb : d70148 p = 1) : d71925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58702 q = 1) (hb : d70148 q = 1) : d71920 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58702, d71920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4529 q ha hb
    | true =>
      simp only [d58702, d71920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58703 q = 1) (hb : d70148 q = 1) : d71921 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58703, d71921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58703, d71921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58704 q = 1) (hb : d70148 q = 1) : d71922 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58704, d71922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58704, d71922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58705 q = 1) (hb : d70148 q = 1) : d71923 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58705, d71923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58705, d71923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58706 q = 1) (hb : d70148 q = 1) : d71924 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58706, d71924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58706, d71924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58707 q = 1) (hb : d70148 q = 1) : d71925 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58707, d71925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58707, d71925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4531 (p : Pattern) (ha : d58713 p = 1) (hb : d70148 p = 1) : d71931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58708 q = 1) (hb : d70148 q = 1) : d71926 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58708, d71926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4530 q ha hb
    | true =>
      simp only [d58708, d71926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58709 q = 1) (hb : d70148 q = 1) : d71927 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58709, d71927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58709, d71927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58710 q = 1) (hb : d70148 q = 1) : d71928 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58710, d71928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58710, d71928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58711 q = 1) (hb : d70148 q = 1) : d71929 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58711, d71929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58711, d71929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58712 q = 1) (hb : d70148 q = 1) : d71930 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58712, d71930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58712, d71930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58713 q = 1) (hb : d70148 q = 1) : d71931 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58713, d71931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58713, d71931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4532 (p : Pattern) (ha : d58719 p = 1) (hb : d70148 p = 1) : d71937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58714 q = 1) (hb : d70148 q = 1) : d71932 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58714, d71932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4531 q ha hb
    | true =>
      simp only [d58714, d71932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58715 q = 1) (hb : d70148 q = 1) : d71933 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58715, d71933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58715, d71933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58716 q = 1) (hb : d70148 q = 1) : d71934 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58716, d71934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58716, d71934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58717 q = 1) (hb : d70148 q = 1) : d71935 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58717, d71935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58717, d71935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58718 q = 1) (hb : d70148 q = 1) : d71936 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58718, d71936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58718, d71936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58719 q = 1) (hb : d70148 q = 1) : d71937 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58719, d71937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58719, d71937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4533 (p : Pattern) (ha : d58725 p = 1) (hb : d70148 p = 1) : d71943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58720 q = 1) (hb : d70148 q = 1) : d71938 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58720, d71938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4532 q ha hb
    | true =>
      simp only [d58720, d71938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58721 q = 1) (hb : d70148 q = 1) : d71939 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58721, d71939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58721, d71939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58722 q = 1) (hb : d70148 q = 1) : d71940 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58722, d71940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58722, d71940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58723 q = 1) (hb : d70148 q = 1) : d71941 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58723, d71941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58723, d71941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58724 q = 1) (hb : d70148 q = 1) : d71942 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58724, d71942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58724, d71942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58725 q = 1) (hb : d70148 q = 1) : d71943 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58725, d71943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58725, d71943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4534 (p : Pattern) (ha : d58731 p = 1) (hb : d70148 p = 1) : d71949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58726 q = 1) (hb : d70148 q = 1) : d71944 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58726, d71944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4533 q ha hb
    | true =>
      simp only [d58726, d71944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58727 q = 1) (hb : d70148 q = 1) : d71945 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58727, d71945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58727, d71945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58728 q = 1) (hb : d70148 q = 1) : d71946 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58728, d71946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58728, d71946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58729 q = 1) (hb : d70148 q = 1) : d71947 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58729, d71947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58729, d71947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58730 q = 1) (hb : d70148 q = 1) : d71948 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58730, d71948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58730, d71948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58731 q = 1) (hb : d70148 q = 1) : d71949 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58731, d71949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58731, d71949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4535 (p : Pattern) (ha : d58737 p = 1) (hb : d70148 p = 1) : d71955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58732 q = 1) (hb : d70148 q = 1) : d71950 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58732, d71950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4534 q ha hb
    | true =>
      simp only [d58732, d71950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58733 q = 1) (hb : d70148 q = 1) : d71951 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58733, d71951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58733, d71951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58734 q = 1) (hb : d70148 q = 1) : d71952 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58734, d71952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58734, d71952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58735 q = 1) (hb : d70148 q = 1) : d71953 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58735, d71953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58735, d71953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58736 q = 1) (hb : d70148 q = 1) : d71954 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58736, d71954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58736, d71954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58737 q = 1) (hb : d70148 q = 1) : d71955 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, d71955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58737, d71955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4536 (p : Pattern) (ha : d58743 p = 1) (hb : d70148 p = 1) : d71961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58738 q = 1) (hb : d70148 q = 1) : d71956 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, d71956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4535 q ha hb
    | true =>
      simp only [d58738, d71956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58739 q = 1) (hb : d70148 q = 1) : d71957 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, d71957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, d71957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58740 q = 1) (hb : d70148 q = 1) : d71958 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, d71958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, d71958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58741 q = 1) (hb : d70148 q = 1) : d71959 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, d71959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, d71959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58742 q = 1) (hb : d70148 q = 1) : d71960 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, d71960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, d71960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58743 q = 1) (hb : d70148 q = 1) : d71961 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58743, d71961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58743, d71961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4537 (p : Pattern) (ha : d42 p = 1) (hb : d70812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40 q = 1) (hb : d70810 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41 q = 1) (hb : d70811 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d70811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41, d70811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, d70812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, d70812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4538 (p : Pattern) (ha : d70817 p = 1) (hb : d71434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4537 q hb ha
  have h3 (q : Pattern) (ha : d70813 q = 1) (hb : d71430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70813, d71430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70813, d71430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70814 q = 1) (hb : d71431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70814, d71431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70814, d71431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70815 q = 1) (hb : d71432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70815, d71432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70815, d71432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70816 q = 1) (hb : d71433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70816, d71433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70816, d71433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70817 q = 1) (hb : d71434 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70817, d71434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70817, d71434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4539 (p : Pattern) (ha : d49 p = 1) (hb : d70818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40 q = 1) (hb : d70810 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41 q = 1) (hb : d70811 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d70811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41, d70811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, d70818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d49, d70818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4540 (p : Pattern) (ha : d70823 p = 1) (hb : d71440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4537 q hb ha
  have h3 (q : Pattern) (ha : d70813 q = 1) (hb : d71430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70813, d71430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70813, d71430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70814 q = 1) (hb : d71431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70814, d71431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70814, d71431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70815 q = 1) (hb : d71432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70815, d71432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70815, d71432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70816 q = 1) (hb : d71433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70816, d71433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70816, d71433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70818 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4539 q hb ha
  have h9 (q : Pattern) (ha : d70819 q = 1) (hb : d71436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70819, d71436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70819, d71436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d70820 q = 1) (hb : d71437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70820, d71437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70820, d71437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70821 q = 1) (hb : d71438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70821, d71438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70821, d71438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70822 q = 1) (hb : d71439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70822, d71439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70822, d71439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70823 q = 1) (hb : d71440 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70823, d71440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70823, d71440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4541 (p : Pattern) (ha : d70828 p = 1) (hb : d71445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70818 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4539 q hb ha
  have h3 (q : Pattern) (ha : d70819 q = 1) (hb : d71436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70819, d71436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70819, d71436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70820 q = 1) (hb : d71437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70820, d71437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70820, d71437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70821 q = 1) (hb : d71438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70821, d71438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70821, d71438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70822 q = 1) (hb : d71439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70822, d71439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70822, d71439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70828 q = 1) (hb : d71445 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70828, d71445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70828, d71445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4542 (p : Pattern) (ha : d83 p = 1) (hb : d70836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81 q = 1) (hb : d70834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, d70834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81, d70834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82 q = 1) (hb : d70835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, d70835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82, d70835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d83 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, d70836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83, d70836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4543 (p : Pattern) (ha : d70841 p = 1) (hb : d71456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70836 q = 1) (hb : d71451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4542 q hb ha
  have h3 (q : Pattern) (ha : d70837 q = 1) (hb : d71452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70837, d71452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70837, d71452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70838 q = 1) (hb : d71453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70838, d71453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70838, d71453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70839 q = 1) (hb : d71454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70839, d71454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70839, d71454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70840 q = 1) (hb : d71455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70840, d71455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70840, d71455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70841 q = 1) (hb : d71456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70841, d71456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70841, d71456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4544 (p : Pattern) (ha : d70847 p = 1) (hb : d71462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70824 q = 1) (hb : d71441 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70824, d71441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4538 q ha hb
    | true =>
      simp only [d70824, d71441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4540 q ha hb
  have h2 (q : Pattern) (ha : d70825 q = 1) (hb : d71442 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70825, d71442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70825, d71442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70826 q = 1) (hb : d71443 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70826, d71443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70826, d71443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70827 q = 1) (hb : d71444 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70827, d71444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70827, d71444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70829 q = 1) (hb : d71446 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70829, d71446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70829, d71446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4541 q ha hb
  have h6 (q : Pattern) (ha : d70830 q = 1) (hb : d71447 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70830, d71447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70830, d71447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70831 q = 1) (hb : d71448 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70831, d71448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70831, d71448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d70832 q = 1) (hb : d71449 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70832, d71449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70832, d71449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d70833 q = 1) (hb : d71450 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70833, d71450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70833, d71450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70842 q = 1) (hb : d71457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70842, d71457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70842, d71457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4543 q ha hb
  have h11 (q : Pattern) (ha : d70843 q = 1) (hb : d71458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70843, d71458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70843, d71458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d70844 q = 1) (hb : d71459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70844, d71459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70844, d71459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d70845 q = 1) (hb : d71460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70845, d71460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70845, d71460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d70846 q = 1) (hb : d71461 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70846, d71461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70846, d71461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d70847 q = 1) (hb : d71462 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70847, d71462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70847, d71462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4545 (p : Pattern) (ha : d70857 p = 1) (hb : d71472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4537 q hb ha
  have h3 (q : Pattern) (ha : d70853 q = 1) (hb : d71468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70853, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70853, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70854 q = 1) (hb : d71469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70854, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70854, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70855 q = 1) (hb : d71470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70855, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70855, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70856 q = 1) (hb : d71471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70856, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70856, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70857 q = 1) (hb : d71472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70857, d71472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70857, d71472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4546 (p : Pattern) (ha : d70864 p = 1) (hb : d71479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4537 q hb ha
  have h3 (q : Pattern) (ha : d70853 q = 1) (hb : d71468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70853, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70853, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70854 q = 1) (hb : d71469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70854, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70854, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70855 q = 1) (hb : d71470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70855, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70855, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70856 q = 1) (hb : d71471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70856, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70856, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70818 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4539 q hb ha
  have h9 (q : Pattern) (ha : d70860 q = 1) (hb : d71475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70860, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70860, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70861 q = 1) (hb : d71476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70861, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70861, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70862 q = 1) (hb : d71477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70862, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70862, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70863 q = 1) (hb : d71478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70863, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70863, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70864 q = 1) (hb : d71479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70864, d71479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70864, d71479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4547 (p : Pattern) (ha : d116 p = 1) (hb : d70869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40 q = 1) (hb : d70810 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115 q = 1) (hb : d70868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, d70868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, d70868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116 q = 1) (hb : d70869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, d70869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, d70869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4548 (p : Pattern) (ha : d123 p = 1) (hb : d70875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121 q = 1) (hb : d70873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d70873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, d70873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122 q = 1) (hb : d70874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, d70874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122, d70874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123 q = 1) (hb : d70875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, d70875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, d70875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4549 (p : Pattern) (ha : d4736 p = 1) (hb : d70880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21 q ha hb
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4733 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4734 q = 1) (hb : d70878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d70878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4734, d70878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4735 q = 1) (hb : d70879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d70879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4735, d70879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4736 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d70880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d70880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4550 (p : Pattern) (ha : d70885 p = 1) (hb : d71495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70869 q = 1) (hb : d71483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4547 q hb ha
  have h3 (q : Pattern) (ha : d70870 q = 1) (hb : d71484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70870, d71484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70870, d71484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70871 q = 1) (hb : d71485 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70871, d71485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70871, d71485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70872 q = 1) (hb : d71486 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70872, d71486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70872, d71486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70875 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70875 q = 1) (hb : d71487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4548 q hb ha
  have h8 (q : Pattern) (ha : d70876 q = 1) (hb : d71488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70876, d71488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70876, d71488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70877 q = 1) (hb : d71489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70877, d71489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70877, d71489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70880 q = 1) (hb : d71490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4549 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70881 q = 1) (hb : d71491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d71491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70881, d71491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70813 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70882 q = 1) (hb : d71492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70882, d71492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70882, d71492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d70883 q = 1) (hb : d71493 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70883, d71493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70883, d71493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d70884 q = 1) (hb : d71494 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70884, d71494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70884, d71494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70885 q = 1) (hb : d71495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70885, d71495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70885, d71495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4551 (p : Pattern) (ha : d194 p = 1) (hb : d70886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40 q = 1) (hb : d70810 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40, d70810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115 q = 1) (hb : d70868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, d70868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, d70868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194 q = 1) (hb : d70886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, d70886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194, d70886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4552 (p : Pattern) (ha : d199 p = 1) (hb : d70890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121 q = 1) (hb : d70873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d70873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, d70873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122 q = 1) (hb : d70874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, d70874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122, d70874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d199 q = 1) (hb : d70890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, d70890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199, d70890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4553 (p : Pattern) (ha : d5355 p = 1) (hb : d70893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21 q ha hb
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4733 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4734 q = 1) (hb : d70878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d70878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4734, d70878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4735 q = 1) (hb : d70879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d70879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4735, d70879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5355 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d70893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5355, d70893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4554 (p : Pattern) (ha : d70898 p = 1) (hb : d71508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70869 q = 1) (hb : d71483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4547 q hb ha
  have h3 (q : Pattern) (ha : d70870 q = 1) (hb : d71484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70870, d71484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70870, d71484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70871 q = 1) (hb : d71485 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70871, d71485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70871, d71485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70872 q = 1) (hb : d71486 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70872, d71486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70872, d71486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70875 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70875 q = 1) (hb : d71487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4548 q hb ha
  have h8 (q : Pattern) (ha : d70876 q = 1) (hb : d71488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70876, d71488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70876, d71488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70877 q = 1) (hb : d71489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70877, d71489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70877, d71489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70880 q = 1) (hb : d71490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4549 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70881 q = 1) (hb : d71491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d71491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70881, d71491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70813 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70882 q = 1) (hb : d71492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70882, d71492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70882, d71492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d70883 q = 1) (hb : d71493 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70883, d71493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70883, d71493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d70884 q = 1) (hb : d71494 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70884, d71494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70884, d71494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d70886 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d70886 q = 1) (hb : d71496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d71496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4551 q hb ha
  have h20 (q : Pattern) (ha : d70887 q = 1) (hb : d71497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70887, d71497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70887, d71497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d70888 q = 1) (hb : d71498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70888, d71498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70888, d71498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70889 q = 1) (hb : d71499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70889, d71499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70889, d71499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d70890 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d70890 q = 1) (hb : d71500 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d71500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4552 q hb ha
  have h25 (q : Pattern) (ha : d70891 q = 1) (hb : d71501 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70891, d71501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70891, d71501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d70892 q = 1) (hb : d71502 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70892, d71502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d70892, d71502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70893 q = 1) (hb : d71503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d71503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4553 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d70894 q = 1) (hb : d71504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d71504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d70894, d71504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d70819 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d70895 q = 1) (hb : d71505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70895, d71505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d70895, d71505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
  have h33 (q : Pattern) (ha : d70896 q = 1) (hb : d71506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70896, d71506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d70896, d71506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d70897 q = 1) (hb : d71507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70897, d71507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d70897, d71507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d70898 q = 1) (hb : d71508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70898, d71508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70898, d71508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro4555 (p : Pattern) (ha : d70905 p = 1) (hb : d71515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70893 q = 1) (hb : d71503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4553 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70894 q = 1) (hb : d71504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d71504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70894, d71504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70819 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70895 q = 1) (hb : d71505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70895, d71505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70895, d71505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d70903 q = 1) (hb : d71513 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70903, d71513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70903, d71513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70904 q = 1) (hb : d71514 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70904, d71514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70904, d71514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70905 q = 1) (hb : d71515 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70905, d71515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70905, d71515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4556 (p : Pattern) (ha : d5377 p = 1) (hb : d70913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25 q ha hb
    | true =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5374 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5375 q = 1) (hb : d70911 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d70911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5375, d70911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5376 q = 1) (hb : d70912 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d70912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5376, d70912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5377 q = 1) (hb : d70913 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d70913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5377, d70913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4557 (p : Pattern) (ha : d70918 p = 1) (hb : d71526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70913 q = 1) (hb : d71521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4556 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70914 q = 1) (hb : d71522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70914, d71522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70914, d71522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70837 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70915 q = 1) (hb : d71523 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70915, d71523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70915, d71523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d70916 q = 1) (hb : d71524 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70916, d71524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70916, d71524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70917 q = 1) (hb : d71525 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70917, d71525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70917, d71525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70918 q = 1) (hb : d71526 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70918, d71526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70918, d71526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4558 (p : Pattern) (ha : d70924 p = 1) (hb : d71532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70858 q = 1) (hb : d71473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70858, d71473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70858, d71473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4545 q ha hb
  have h2 (q : Pattern) (ha : d70859 q = 1) (hb : d71474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70859, d71474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70859, d71474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70865 q = 1) (hb : d71480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70865, d71480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4545 q ha hb
    | true =>
      simp only [d70865, d71480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4546 q ha hb
  have h4 (q : Pattern) (ha : d70866 q = 1) (hb : d71481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70866, d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70866, d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70867 q = 1) (hb : d71482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70867, d71482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70867, d71482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70899 q = 1) (hb : d71509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70899, d71509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4550 q ha hb
    | true =>
      simp only [d70899, d71509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4554 q ha hb
  have h7 (q : Pattern) (ha : d70900 q = 1) (hb : d71510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70900, d71510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70900, d71510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d70901 q = 1) (hb : d71511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70901, d71511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70901, d71511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d70902 q = 1) (hb : d71512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70902, d71512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70902, d71512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70906 q = 1) (hb : d71516 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70906, d71516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70906, d71516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4555 q ha hb
  have h11 (q : Pattern) (ha : d70907 q = 1) (hb : d71517 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70907, d71517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70907, d71517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d70908 q = 1) (hb : d71518 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70908, d71518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70908, d71518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d70909 q = 1) (hb : d71519 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70909, d71519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70909, d71519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d70910 q = 1) (hb : d71520 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70910, d71520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70910, d71520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70919 q = 1) (hb : d71527 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70919, d71527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70919, d71527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4557 q ha hb
  have h16 (q : Pattern) (ha : d70920 q = 1) (hb : d71528 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70920, d71528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70920, d71528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70921 q = 1) (hb : d71529 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70921, d71529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70921, d71529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d70922 q = 1) (hb : d71530 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70922, d71530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70922, d71530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d70923 q = 1) (hb : d71531 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70923, d71531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d70923, d71531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d70924 q = 1) (hb : d71532 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70924, d71532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70924, d71532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4559 (p : Pattern) (ha : d70930 p = 1) (hb : d71538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70848 q = 1) (hb : d71463 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70848, d71463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70848, d71463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4544 q ha hb
  have h2 (q : Pattern) (ha : d70849 q = 1) (hb : d71464 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70849, d71464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70849, d71464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70850 q = 1) (hb : d71465 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70850, d71465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70850, d71465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70851 q = 1) (hb : d71466 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70851, d71466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70851, d71466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70852 q = 1) (hb : d71467 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70852, d71467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70852, d71467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70925 q = 1) (hb : d71533 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70925, d71533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70925, d71533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4558 q ha hb
  have h7 (q : Pattern) (ha : d70926 q = 1) (hb : d71534 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70926, d71534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70926, d71534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70927 q = 1) (hb : d71535 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70927, d71535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70927, d71535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70928 q = 1) (hb : d71536 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70928, d71536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70928, d71536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70929 q = 1) (hb : d71537 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70929, d71537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70929, d71537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70930 q = 1) (hb : d71538 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70930, d71538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70930, d71538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4560 (p : Pattern) (ha : d491 p = 1) (hb : d70933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d489 q = 1) (hb : d70931 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d490 q = 1) (hb : d70932 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d70932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d490, d70932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d491 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d70933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d70933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4561 (p : Pattern) (ha : d70938 p = 1) (hb : d71544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70933 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4560 q hb ha
  have h3 (q : Pattern) (ha : d70934 q = 1) (hb : d71540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70934, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70934, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70935 q = 1) (hb : d71541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70935, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70935, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70936 q = 1) (hb : d71542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70936, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70936, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70937 q = 1) (hb : d71543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70937, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70937, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70938 q = 1) (hb : d71544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70938, d71544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70938, d71544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4562 (p : Pattern) (ha : d501 p = 1) (hb : d70941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d489 q = 1) (hb : d70931 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d490 q = 1) (hb : d70932 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d70932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d490, d70932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d70941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d501, d70941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4563 (p : Pattern) (ha : d70946 p = 1) (hb : d71552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70933 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4560 q hb ha
  have h3 (q : Pattern) (ha : d70934 q = 1) (hb : d71540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70934, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70934, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70935 q = 1) (hb : d71541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70935, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70935, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70936 q = 1) (hb : d71542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70936, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70936, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70937 q = 1) (hb : d71543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70937, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70937, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70941 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4562 q hb ha
  have h9 (q : Pattern) (ha : d70942 q = 1) (hb : d71548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70942, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70942, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70943 q = 1) (hb : d71549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70943, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70943, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70944 q = 1) (hb : d71550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70944, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70944, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70945 q = 1) (hb : d71551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70945, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70945, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70946 q = 1) (hb : d71552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70946, d71552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70946, d71552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4564 (p : Pattern) (ha : d514 p = 1) (hb : d70951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d489 q = 1) (hb : d70931 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d513 q = 1) (hb : d70950 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d70950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d70950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d514 q = 1) (hb : d70951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d70951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d70951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4565 (p : Pattern) (ha : d524 p = 1) (hb : d70957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d522 q = 1) (hb : d70955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d70955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d70955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d523 q = 1) (hb : d70956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d70956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d523, d70956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d524 q = 1) (hb : d70957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d70957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d70957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4566 (p : Pattern) (ha : d5399 p = 1) (hb : d70962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60 q ha hb
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5396 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5397 q = 1) (hb : d70960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d70960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5397, d70960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5398 q = 1) (hb : d70961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d70961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5398, d70961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5399 q = 1) (hb : d70962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d70962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d70962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4567 (p : Pattern) (ha : d70968 p = 1) (hb : d71568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70951 q = 1) (hb : d71556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4564 q hb ha
  have h3 (q : Pattern) (ha : d70952 q = 1) (hb : d71557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70952, d71557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70952, d71557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70953 q = 1) (hb : d71558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70953, d71558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70953, d71558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70954 q = 1) (hb : d71559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70954, d71559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70954, d71559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70957 q = 1) (hb : d71560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4565 q hb ha
  have h8 (q : Pattern) (ha : d70958 q = 1) (hb : d71561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70958, d71561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70958, d71561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70959 q = 1) (hb : d71562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70959, d71562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70959, d71562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70962 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70962 q = 1) (hb : d71563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4566 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70963 q = 1) (hb : d71564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70963, d71564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70963, d71564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70965 q = 1) (hb : d71565 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70965, d71565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70965, d71565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d70966 q = 1) (hb : d71566 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70966, d71566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70966, d71566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d70967 q = 1) (hb : d71567 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70967, d71567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70967, d71567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70968 q = 1) (hb : d71568 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70968, d71568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70968, d71568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4568 (p : Pattern) (ha : d610 p = 1) (hb : d70969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d489 q = 1) (hb : d70931 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d489, d70931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d513 q = 1) (hb : d70950 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d70950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d70950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d610 q = 1) (hb : d70969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d70969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d610, d70969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4569 (p : Pattern) (ha : d616 p = 1) (hb : d70973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d522 q = 1) (hb : d70955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d70955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d70955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d523 q = 1) (hb : d70956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d70956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d523, d70956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d616 q = 1) (hb : d70973 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d70973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d616, d70973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4570 (p : Pattern) (ha : d5406 p = 1) (hb : d70976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60 q ha hb
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5396 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5397 q = 1) (hb : d70960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d70960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5397, d70960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5398 q = 1) (hb : d70961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d70961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5398, d70961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5406 q = 1) (hb : d70976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d70976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5406, d70976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4571 (p : Pattern) (ha : d70982 p = 1) (hb : d71581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70951 q = 1) (hb : d71556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4564 q hb ha
  have h3 (q : Pattern) (ha : d70952 q = 1) (hb : d71557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70952, d71557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70952, d71557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70953 q = 1) (hb : d71558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70953, d71558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70953, d71558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70954 q = 1) (hb : d71559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70954, d71559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70954, d71559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70957 q = 1) (hb : d71560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4565 q hb ha
  have h8 (q : Pattern) (ha : d70958 q = 1) (hb : d71561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70958, d71561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70958, d71561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70959 q = 1) (hb : d71562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70959, d71562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70959, d71562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70962 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70962 q = 1) (hb : d71563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4566 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70963 q = 1) (hb : d71564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70963, d71564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70963, d71564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70965 q = 1) (hb : d71565 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70965, d71565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70965, d71565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d70966 q = 1) (hb : d71566 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70966, d71566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70966, d71566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d70967 q = 1) (hb : d71567 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70967, d71567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70967, d71567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d70969 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d70969 q = 1) (hb : d71569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d71569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4568 q hb ha
  have h20 (q : Pattern) (ha : d70970 q = 1) (hb : d71570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70970, d71570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70970, d71570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d70971 q = 1) (hb : d71571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70971, d71571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70971, d71571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70972 q = 1) (hb : d71572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70972, d71572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70972, d71572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d70973 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d70973 q = 1) (hb : d71573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d71573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4569 q hb ha
  have h25 (q : Pattern) (ha : d70974 q = 1) (hb : d71574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70974, d71574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70974, d71574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d70975 q = 1) (hb : d71575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70975, d71575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d70975, d71575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d70976 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70976 q = 1) (hb : d71576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d71576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4570 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d70977 q = 1) (hb : d71577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70977, d71577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d70977, d71577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d70978 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d70979 q = 1) (hb : d71578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70979, d71578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d70979, d71578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
  have h33 (q : Pattern) (ha : d70980 q = 1) (hb : d71579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70980, d71579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d70980, d71579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d70981 q = 1) (hb : d71580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70981, d71580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d70981, d71580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d70982 q = 1) (hb : d71581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70982, d71581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70982, d71581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro4572 (p : Pattern) (ha : d70989 p = 1) (hb : d71588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70976 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70976 q = 1) (hb : d71576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4570 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70977 q = 1) (hb : d71577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70977, d71577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70977, d71577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70978 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70979 q = 1) (hb : d71578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70979, d71578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70979, d71578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d70987 q = 1) (hb : d71586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70987, d71586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70987, d71586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70988 q = 1) (hb : d71587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70988, d71587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70988, d71587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70989 q = 1) (hb : d71588 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70989, d71588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70989, d71588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4573 (p : Pattern) (ha : d5428 p = 1) (hb : d70997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83 q ha hb
    | true =>
      simp only [d676, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5425 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5426 q = 1) (hb : d70995 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d70995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5426, d70995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5427 q = 1) (hb : d70996 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d70996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5427, d70996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5428 q = 1) (hb : d70997 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d70997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5428, d70997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4574 (p : Pattern) (ha : d71006 p = 1) (hb : d71599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70997 q = 1) (hb : d71594 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4573 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71000 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71001 q = 1) (hb : d71595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71001, d71595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71001, d71595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71002 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71003 q = 1) (hb : d71596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71003, d71596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71003, d71596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71004 q = 1) (hb : d71597 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71004, d71597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71004, d71597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71005 q = 1) (hb : d71598 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71005, d71598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71005, d71598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71006 q = 1) (hb : d71599 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71006, d71599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71006, d71599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4575 (p : Pattern) (ha : d71012 p = 1) (hb : d71605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70939 q = 1) (hb : d71545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70939, d71545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70939, d71545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4561 q ha hb
  have h2 (q : Pattern) (ha : d70940 q = 1) (hb : d71546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70940, d71546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70940, d71546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70947 q = 1) (hb : d71553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70947, d71553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4561 q ha hb
    | true =>
      simp only [d70947, d71553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4563 q ha hb
  have h4 (q : Pattern) (ha : d70948 q = 1) (hb : d71554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70948, d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70948, d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70949 q = 1) (hb : d71555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70949, d71555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70949, d71555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70983 q = 1) (hb : d71582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70983, d71582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4567 q ha hb
    | true =>
      simp only [d70983, d71582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4571 q ha hb
  have h7 (q : Pattern) (ha : d70984 q = 1) (hb : d71583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70984, d71583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70984, d71583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d70985 q = 1) (hb : d71584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70985, d71584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70985, d71584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d70986 q = 1) (hb : d71585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70986, d71585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70986, d71585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70990 q = 1) (hb : d71589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70990, d71589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70990, d71589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4572 q ha hb
  have h11 (q : Pattern) (ha : d70991 q = 1) (hb : d71590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70991, d71590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70991, d71590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d70992 q = 1) (hb : d71591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70992, d71591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70992, d71591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d70993 q = 1) (hb : d71592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70993, d71592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70993, d71592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d70994 q = 1) (hb : d71593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70994, d71593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70994, d71593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71007 q = 1) (hb : d71600 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71007, d71600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71007, d71600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4574 q ha hb
  have h16 (q : Pattern) (ha : d71008 q = 1) (hb : d71601 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71008, d71601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71008, d71601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d71009 q = 1) (hb : d71602 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71009, d71602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d71009, d71602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d71010 q = 1) (hb : d71603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71010, d71603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71010, d71603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d71011 q = 1) (hb : d71604 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71011, d71604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d71011, d71604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d71012 q = 1) (hb : d71605 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71012, d71605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71012, d71605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4576 (p : Pattern) (ha : d71018 p = 1) (hb : d71611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71013 q = 1) (hb : d71606 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71013, d71606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71013, d71606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4575 q ha hb
  have h2 (q : Pattern) (ha : d71014 q = 1) (hb : d71607 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71014, d71607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71014, d71607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71015 q = 1) (hb : d71608 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71015, d71608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71015, d71608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71016 q = 1) (hb : d71609 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71016, d71609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71016, d71609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71017 q = 1) (hb : d71610 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71017, d71610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71017, d71610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71018 q = 1) (hb : d71611 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71018, d71611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71018, d71611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4577 (p : Pattern) (ha : d783 p = 1) (hb : d71022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d71020 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d782 q = 1) (hb : d71021 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d71021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d782, d71021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d783 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d71022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d71022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4578 (p : Pattern) (ha : d71027 p = 1) (hb : d71618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71022 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4577 q hb ha
  have h3 (q : Pattern) (ha : d71023 q = 1) (hb : d71614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71023, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71023, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71024 q = 1) (hb : d71615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71024, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71024, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71025 q = 1) (hb : d71616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71025, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71025, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71026 q = 1) (hb : d71617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71026, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71026, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71027 q = 1) (hb : d71618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71027, d71618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71027, d71618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4579 (p : Pattern) (ha : d793 p = 1) (hb : d71030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d71020 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d782 q = 1) (hb : d71021 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d71021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d782, d71021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d71030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d793, d71030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4580 (p : Pattern) (ha : d71035 p = 1) (hb : d71626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71022 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4577 q hb ha
  have h3 (q : Pattern) (ha : d71023 q = 1) (hb : d71614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71023, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71023, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71024 q = 1) (hb : d71615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71024, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71024, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71025 q = 1) (hb : d71616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71025, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71025, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71026 q = 1) (hb : d71617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71026, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71026, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71030 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4579 q hb ha
  have h9 (q : Pattern) (ha : d71031 q = 1) (hb : d71622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71031, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71031, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71032 q = 1) (hb : d71623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71032, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71032, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71033 q = 1) (hb : d71624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71033, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71033, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71034 q = 1) (hb : d71625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71034, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71034, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71035 q = 1) (hb : d71626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71035, d71626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71035, d71626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4581 (p : Pattern) (ha : d806 p = 1) (hb : d71040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d71020 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d805 q = 1) (hb : d71039 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d71039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d71039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d806 q = 1) (hb : d71040 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d71040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d71040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4582 (p : Pattern) (ha : d816 p = 1) (hb : d71046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d814 q = 1) (hb : d71044 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d71044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d71044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d815 q = 1) (hb : d71045 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d71045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d815, d71045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d816 q = 1) (hb : d71046 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d71046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d71046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4583 (p : Pattern) (ha : d6118 p = 1) (hb : d71051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104 q ha hb
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6115 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6116 q = 1) (hb : d71049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d71049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6116, d71049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6117 q = 1) (hb : d71050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d71050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6117, d71050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6118 q = 1) (hb : d71051 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6118, d71051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6118, d71051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4584 (p : Pattern) (ha : d71057 p = 1) (hb : d71642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71040 q = 1) (hb : d71630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4581 q hb ha
  have h3 (q : Pattern) (ha : d71041 q = 1) (hb : d71631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71041, d71631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71041, d71631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71042 q = 1) (hb : d71632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71042, d71632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71042, d71632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71043 q = 1) (hb : d71633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71043, d71633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71043, d71633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71046 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71046 q = 1) (hb : d71634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4582 q hb ha
  have h8 (q : Pattern) (ha : d71047 q = 1) (hb : d71635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71047, d71635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71047, d71635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71048 q = 1) (hb : d71636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71048, d71636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71048, d71636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71051 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71051 q = 1) (hb : d71637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4583 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71052 q = 1) (hb : d71638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71052, d71638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71052, d71638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71053 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71054 q = 1) (hb : d71639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71054, d71639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71054, d71639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71055 q = 1) (hb : d71640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71055, d71640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71055, d71640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71056 q = 1) (hb : d71641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71056, d71641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71056, d71641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71057 q = 1) (hb : d71642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71057, d71642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71057, d71642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4585 (p : Pattern) (ha : d916 p = 1) (hb : d71058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d71020 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, d71020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d805 q = 1) (hb : d71039 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d71039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d71039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d916 q = 1) (hb : d71058 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d71058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d916, d71058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4586 (p : Pattern) (ha : d922 p = 1) (hb : d71062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d814 q = 1) (hb : d71044 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d71044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d71044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d815 q = 1) (hb : d71045 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d71045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d815, d71045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d922 q = 1) (hb : d71062 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d71062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d922, d71062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4587 (p : Pattern) (ha : d6127 p = 1) (hb : d71065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104 q ha hb
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6115 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6116 q = 1) (hb : d71049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d71049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6116, d71049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6117 q = 1) (hb : d71050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d71050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6117, d71050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6127 q = 1) (hb : d71065 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6127, d71065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6127, d71065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4588 (p : Pattern) (ha : d71071 p = 1) (hb : d71655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71040 q = 1) (hb : d71630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4581 q hb ha
  have h3 (q : Pattern) (ha : d71041 q = 1) (hb : d71631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71041, d71631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71041, d71631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71042 q = 1) (hb : d71632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71042, d71632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71042, d71632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71043 q = 1) (hb : d71633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71043, d71633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71043, d71633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71046 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71046 q = 1) (hb : d71634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4582 q hb ha
  have h8 (q : Pattern) (ha : d71047 q = 1) (hb : d71635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71047, d71635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71047, d71635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71048 q = 1) (hb : d71636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71048, d71636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71048, d71636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71051 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71051 q = 1) (hb : d71637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4583 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71052 q = 1) (hb : d71638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71052, d71638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71052, d71638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71053 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71054 q = 1) (hb : d71639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71054, d71639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71054, d71639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71055 q = 1) (hb : d71640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71055, d71640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71055, d71640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71056 q = 1) (hb : d71641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71056, d71641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71056, d71641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d71058 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d71058 q = 1) (hb : d71643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d71643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4585 q hb ha
  have h20 (q : Pattern) (ha : d71059 q = 1) (hb : d71644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71059, d71644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71059, d71644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d71060 q = 1) (hb : d71645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71060, d71645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d71060, d71645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d71061 q = 1) (hb : d71646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71061, d71646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71061, d71646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d71062 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d71062 q = 1) (hb : d71647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d71647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4586 q hb ha
  have h25 (q : Pattern) (ha : d71063 q = 1) (hb : d71648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71063, d71648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71063, d71648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d71064 q = 1) (hb : d71649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71064, d71649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d71064, d71649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d71065 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d71065 q = 1) (hb : d71650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d71650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4587 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d71066 q = 1) (hb : d71651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71066, d71651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d71066, d71651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d71067 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d71068 q = 1) (hb : d71652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71068, d71652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d71068, d71652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
  have h33 (q : Pattern) (ha : d71069 q = 1) (hb : d71653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71069, d71653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d71069, d71653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d71070 q = 1) (hb : d71654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71070, d71654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d71070, d71654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d71071 q = 1) (hb : d71655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71071, d71655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71071, d71655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro4589 (p : Pattern) (ha : d71078 p = 1) (hb : d71662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71065 q = 1) (hb : d71650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4587 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71066 q = 1) (hb : d71651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71066, d71651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71066, d71651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71068 q = 1) (hb : d71652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71068, d71652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71068, d71652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71076 q = 1) (hb : d71660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71076, d71660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71076, d71660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71077 q = 1) (hb : d71661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71077, d71661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71077, d71661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71078 q = 1) (hb : d71662 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71078, d71662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71078, d71662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4590 (p : Pattern) (ha : d6233 p = 1) (hb : d71086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro130 q ha hb
    | true =>
      simp only [d998, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6230 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6231 q = 1) (hb : d71084 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d71084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6231, d71084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6232 q = 1) (hb : d71085 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d71085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6232, d71085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6233 q = 1) (hb : d71086 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d71086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6233, d71086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4591 (p : Pattern) (ha : d71095 p = 1) (hb : d71673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71086 q = 1) (hb : d71668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4590 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71089 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71090 q = 1) (hb : d71669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71090, d71669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71090, d71669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71091 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71092 q = 1) (hb : d71670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71092, d71670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71092, d71670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71093 q = 1) (hb : d71671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71093, d71671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71093, d71671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71094 q = 1) (hb : d71672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71094, d71672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71094, d71672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71095 q = 1) (hb : d71673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71095, d71673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71095, d71673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4592 (p : Pattern) (ha : d71101 p = 1) (hb : d71679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71028 q = 1) (hb : d71619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71028, d71619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71028, d71619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4578 q ha hb
  have h2 (q : Pattern) (ha : d71029 q = 1) (hb : d71620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71029, d71620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71029, d71620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71036 q = 1) (hb : d71627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71036, d71627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4578 q ha hb
    | true =>
      simp only [d71036, d71627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4580 q ha hb
  have h4 (q : Pattern) (ha : d71037 q = 1) (hb : d71628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71037, d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71037, d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71038 q = 1) (hb : d71629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71038, d71629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71038, d71629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71072 q = 1) (hb : d71656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71072, d71656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4584 q ha hb
    | true =>
      simp only [d71072, d71656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4588 q ha hb
  have h7 (q : Pattern) (ha : d71073 q = 1) (hb : d71657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71073, d71657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71073, d71657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d71074 q = 1) (hb : d71658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71074, d71658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71074, d71658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d71075 q = 1) (hb : d71659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71075, d71659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71075, d71659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71079 q = 1) (hb : d71663 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71079, d71663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71079, d71663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4589 q ha hb
  have h11 (q : Pattern) (ha : d71080 q = 1) (hb : d71664 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71080, d71664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71080, d71664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d71081 q = 1) (hb : d71665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71081, d71665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71081, d71665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d71082 q = 1) (hb : d71666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71082, d71666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71082, d71666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d71083 q = 1) (hb : d71667 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71083, d71667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71083, d71667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71096 q = 1) (hb : d71674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71096, d71674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71096, d71674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4591 q ha hb
  have h16 (q : Pattern) (ha : d71097 q = 1) (hb : d71675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71097, d71675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71097, d71675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d71098 q = 1) (hb : d71676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71098, d71676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d71098, d71676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d71099 q = 1) (hb : d71677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71099, d71677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71099, d71677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d71100 q = 1) (hb : d71678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71100, d71678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d71100, d71678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d71101 q = 1) (hb : d71679 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71101, d71679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71101, d71679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4593 (p : Pattern) (ha : d71107 p = 1) (hb : d71685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71102 q = 1) (hb : d71680 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71102, d71680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71102, d71680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4592 q ha hb
  have h2 (q : Pattern) (ha : d71103 q = 1) (hb : d71681 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71103, d71681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71103, d71681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71104 q = 1) (hb : d71682 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71104, d71682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71104, d71682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71105 q = 1) (hb : d71683 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71105, d71683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71105, d71683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71106 q = 1) (hb : d71684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71106, d71684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71106, d71684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71107 q = 1) (hb : d71685 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71107, d71685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71107, d71685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4594 (p : Pattern) (ha : d1162 p = 1) (hb : d71112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d71110 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1161 q = 1) (hb : d71111 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d71111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1161, d71111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1162 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d71112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d71112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4595 (p : Pattern) (ha : d71117 p = 1) (hb : d71693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71112 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4594 q hb ha
  have h3 (q : Pattern) (ha : d71113 q = 1) (hb : d71689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71113, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71113, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71114 q = 1) (hb : d71690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71114, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71114, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71115 q = 1) (hb : d71691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71115, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71115, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71116 q = 1) (hb : d71692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71116, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71116, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71117 q = 1) (hb : d71693 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71117, d71693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71117, d71693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4596 (p : Pattern) (ha : d1172 p = 1) (hb : d71120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d71110 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1161 q = 1) (hb : d71111 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d71111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1161, d71111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d71120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1172, d71120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4597 (p : Pattern) (ha : d71125 p = 1) (hb : d71701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71112 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4594 q hb ha
  have h3 (q : Pattern) (ha : d71113 q = 1) (hb : d71689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71113, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71113, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71114 q = 1) (hb : d71690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71114, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71114, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71115 q = 1) (hb : d71691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71115, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71115, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71116 q = 1) (hb : d71692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71116, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71116, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71120 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4596 q hb ha
  have h9 (q : Pattern) (ha : d71121 q = 1) (hb : d71697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71121, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71121, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71122 q = 1) (hb : d71698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71122, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71122, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71123 q = 1) (hb : d71699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71123, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71123, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71124 q = 1) (hb : d71700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71124, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71124, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71125 q = 1) (hb : d71701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71125, d71701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71125, d71701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4598 (p : Pattern) (ha : d1185 p = 1) (hb : d71130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d71110 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1184 q = 1) (hb : d71129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d71129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d71129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1185 q = 1) (hb : d71130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d71130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d71130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4599 (p : Pattern) (ha : d1195 p = 1) (hb : d71136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1193 q = 1) (hb : d71134 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d71134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d71134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1194 q = 1) (hb : d71135 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d71135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1194, d71135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1195 q = 1) (hb : d71136 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d71136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d71136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4600 (p : Pattern) (ha : d6257 p = 1) (hb : d71141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro156 q ha hb
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6254 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6255 q = 1) (hb : d71139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d71139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6255, d71139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6256 q = 1) (hb : d71140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d71140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6256, d71140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6257 q = 1) (hb : d71141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, d71141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6257, d71141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4601 (p : Pattern) (ha : d71147 p = 1) (hb : d71717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71130 q = 1) (hb : d71705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4598 q hb ha
  have h3 (q : Pattern) (ha : d71131 q = 1) (hb : d71706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71131, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71131, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71132 q = 1) (hb : d71707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71132, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71132, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71133 q = 1) (hb : d71708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71133, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71133, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71136 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71136 q = 1) (hb : d71709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4599 q hb ha
  have h8 (q : Pattern) (ha : d71137 q = 1) (hb : d71710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71137, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71137, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71138 q = 1) (hb : d71711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71138, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71138, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71141 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71141 q = 1) (hb : d71712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4600 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71142 q = 1) (hb : d71713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71142, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71142, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71143 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71144 q = 1) (hb : d71714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71144, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71144, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71145 q = 1) (hb : d71715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71145, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71145, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71146 q = 1) (hb : d71716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71146, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71146, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71147 q = 1) (hb : d71717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71147, d71717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71147, d71717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4602 (p : Pattern) (ha : d1327 p = 1) (hb : d71148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d71110 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, d71110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1184 q = 1) (hb : d71129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d71129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d71129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1327 q = 1) (hb : d71148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d71148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1327, d71148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4603 (p : Pattern) (ha : d1333 p = 1) (hb : d71152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1193 q = 1) (hb : d71134 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d71134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d71134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1194 q = 1) (hb : d71135 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d71135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1194, d71135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1333 q = 1) (hb : d71152 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d71152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1333, d71152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4604 (p : Pattern) (ha : d6266 p = 1) (hb : d71155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro156 q ha hb
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6254 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6255 q = 1) (hb : d71139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d71139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6255, d71139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6256 q = 1) (hb : d71140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d71140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6256, d71140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6266 q = 1) (hb : d71155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, d71155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6266, d71155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4605 (p : Pattern) (ha : d71161 p = 1) (hb : d71730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71130 q = 1) (hb : d71705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4598 q hb ha
  have h3 (q : Pattern) (ha : d71131 q = 1) (hb : d71706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71131, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71131, d71706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71132 q = 1) (hb : d71707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71132, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71132, d71707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71133 q = 1) (hb : d71708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71133, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71133, d71708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71136 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71136 q = 1) (hb : d71709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4599 q hb ha
  have h8 (q : Pattern) (ha : d71137 q = 1) (hb : d71710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71137, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71137, d71710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71138 q = 1) (hb : d71711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71138, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71138, d71711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71141 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71141 q = 1) (hb : d71712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4600 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71142 q = 1) (hb : d71713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71142, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71142, d71713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71143 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71144 q = 1) (hb : d71714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71144, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71144, d71714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71145 q = 1) (hb : d71715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71145, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71145, d71715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71146 q = 1) (hb : d71716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71146, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71146, d71716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d71148 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d71148 q = 1) (hb : d71718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d71718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4602 q hb ha
  have h20 (q : Pattern) (ha : d71149 q = 1) (hb : d71719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71149, d71719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71149, d71719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d71150 q = 1) (hb : d71720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71150, d71720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d71150, d71720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d71151 q = 1) (hb : d71721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71151, d71721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71151, d71721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d71152 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d71152 q = 1) (hb : d71722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d71722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4603 q hb ha
  have h25 (q : Pattern) (ha : d71153 q = 1) (hb : d71723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71153, d71723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71153, d71723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d71154 q = 1) (hb : d71724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71154, d71724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d71154, d71724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d71155 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d71155 q = 1) (hb : d71725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d71725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4604 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d71156 q = 1) (hb : d71726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71156, d71726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d71156, d71726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d71157 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d71158 q = 1) (hb : d71727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71158, d71727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d71158, d71727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
  have h33 (q : Pattern) (ha : d71159 q = 1) (hb : d71728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71159, d71728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d71159, d71728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d71160 q = 1) (hb : d71729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71160, d71729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d71160, d71729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d71161 q = 1) (hb : d71730 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71161, d71730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71161, d71730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro4606 (p : Pattern) (ha : d71168 p = 1) (hb : d71737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71155 q = 1) (hb : d71725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4604 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71156 q = 1) (hb : d71726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71156, d71726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71156, d71726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71158 q = 1) (hb : d71727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71158, d71727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71158, d71727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71166 q = 1) (hb : d71735 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71166, d71735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71166, d71735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71167 q = 1) (hb : d71736 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71167, d71736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71167, d71736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71168 q = 1) (hb : d71737 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71168, d71737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71168, d71737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4607 (p : Pattern) (ha : d6378 p = 1) (hb : d71176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro182 q ha hb
    | true =>
      simp only [d1423, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6375 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6376 q = 1) (hb : d71174 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d71174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6376, d71174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6377 q = 1) (hb : d71175 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d71175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6377, d71175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6378 q = 1) (hb : d71176 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d71176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6378, d71176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4608 (p : Pattern) (ha : d71185 p = 1) (hb : d71748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71176 q = 1) (hb : d71743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4607 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71179 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71180 q = 1) (hb : d71744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71180, d71744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71180, d71744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71182 q = 1) (hb : d71745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71182, d71745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71182, d71745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71183 q = 1) (hb : d71746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71183, d71746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71183, d71746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71184 q = 1) (hb : d71747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71184, d71747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71184, d71747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71185 q = 1) (hb : d71748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71185, d71748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71185, d71748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4609 (p : Pattern) (ha : d71191 p = 1) (hb : d71754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71118 q = 1) (hb : d71694 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71118, d71694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71118, d71694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4595 q ha hb
  have h2 (q : Pattern) (ha : d71119 q = 1) (hb : d71695 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71119, d71695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71119, d71695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71126 q = 1) (hb : d71702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71126, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4595 q ha hb
    | true =>
      simp only [d71126, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4597 q ha hb
  have h4 (q : Pattern) (ha : d71127 q = 1) (hb : d71703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71127, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71127, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71128 q = 1) (hb : d71704 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71128, d71704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71128, d71704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71162 q = 1) (hb : d71731 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71162, d71731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4601 q ha hb
    | true =>
      simp only [d71162, d71731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4605 q ha hb
  have h7 (q : Pattern) (ha : d71163 q = 1) (hb : d71732 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71163, d71732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71163, d71732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d71164 q = 1) (hb : d71733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71164, d71733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71164, d71733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d71165 q = 1) (hb : d71734 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71165, d71734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71165, d71734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71169 q = 1) (hb : d71738 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71169, d71738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71169, d71738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4606 q ha hb
  have h11 (q : Pattern) (ha : d71170 q = 1) (hb : d71739 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71170, d71739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71170, d71739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d71171 q = 1) (hb : d71740 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71171, d71740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71171, d71740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d71172 q = 1) (hb : d71741 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71172, d71741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71172, d71741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d71173 q = 1) (hb : d71742 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71173, d71742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71173, d71742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71186 q = 1) (hb : d71749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71186, d71749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71186, d71749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4608 q ha hb
  have h16 (q : Pattern) (ha : d71187 q = 1) (hb : d71750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71187, d71750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71187, d71750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d71188 q = 1) (hb : d71751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71188, d71751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d71188, d71751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d71189 q = 1) (hb : d71752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71189, d71752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71189, d71752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d71190 q = 1) (hb : d71753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71190, d71753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d71190, d71753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d71191 q = 1) (hb : d71754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71191, d71754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71191, d71754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4610 (p : Pattern) (ha : d71197 p = 1) (hb : d71760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71192 q = 1) (hb : d71755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71192, d71755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71192, d71755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4609 q ha hb
  have h2 (q : Pattern) (ha : d71193 q = 1) (hb : d71756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71193, d71756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71193, d71756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71194 q = 1) (hb : d71757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71194, d71757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71194, d71757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71195 q = 1) (hb : d71758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71195, d71758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71195, d71758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71196 q = 1) (hb : d71759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71196, d71759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71196, d71759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71197 q = 1) (hb : d71760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71197, d71760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71197, d71760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4611 (p : Pattern) (ha : d1623 p = 1) (hb : d71203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d71201 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1622 q = 1) (hb : d71202 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d71202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1622, d71202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1623 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d71203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d71203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4612 (p : Pattern) (ha : d71208 p = 1) (hb : d71769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71203 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4611 q hb ha
  have h3 (q : Pattern) (ha : d71204 q = 1) (hb : d71765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71204, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71204, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71205 q = 1) (hb : d71766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71205, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71205, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71206 q = 1) (hb : d71767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71206, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71206, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71207 q = 1) (hb : d71768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71207, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71207, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71208 q = 1) (hb : d71769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71208, d71769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71208, d71769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4613 (p : Pattern) (ha : d1633 p = 1) (hb : d71211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d71201 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1622 q = 1) (hb : d71202 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d71202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1622, d71202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d71211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1633, d71211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4614 (p : Pattern) (ha : d71216 p = 1) (hb : d71777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71203 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4611 q hb ha
  have h3 (q : Pattern) (ha : d71204 q = 1) (hb : d71765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71204, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71204, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71205 q = 1) (hb : d71766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71205, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71205, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71206 q = 1) (hb : d71767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71206, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71206, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71207 q = 1) (hb : d71768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71207, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71207, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71211 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4613 q hb ha
  have h9 (q : Pattern) (ha : d71212 q = 1) (hb : d71773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71212, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71212, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71213 q = 1) (hb : d71774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71213, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71213, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71214 q = 1) (hb : d71775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71214, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71214, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71215 q = 1) (hb : d71776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71215, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71215, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71216 q = 1) (hb : d71777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71216, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71216, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4615 (p : Pattern) (ha : d1646 p = 1) (hb : d71221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d71201 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1645 q = 1) (hb : d71220 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d71220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d71220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1646 q = 1) (hb : d71221 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d71221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d71221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4616 (p : Pattern) (ha : d1656 p = 1) (hb : d71227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1654 q = 1) (hb : d71225 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d71225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d71225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1655 q = 1) (hb : d71226 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d71226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1655, d71226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1656 q = 1) (hb : d71227 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d71227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d71227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4617 (p : Pattern) (ha : d6403 p = 1) (hb : d71232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro214 q ha hb
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6400 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6401 q = 1) (hb : d71230 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d71230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6401, d71230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6402 q = 1) (hb : d71231 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d71231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6402, d71231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6403 q = 1) (hb : d71232 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, d71232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6403, d71232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4618 (p : Pattern) (ha : d71238 p = 1) (hb : d71793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71221 q = 1) (hb : d71781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4615 q hb ha
  have h3 (q : Pattern) (ha : d71222 q = 1) (hb : d71782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71222, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71222, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71223 q = 1) (hb : d71783 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71223, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71223, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71224 q = 1) (hb : d71784 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71224, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71224, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71227 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71227 q = 1) (hb : d71785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4616 q hb ha
  have h8 (q : Pattern) (ha : d71228 q = 1) (hb : d71786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71228, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71228, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71229 q = 1) (hb : d71787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71229, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71229, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71232 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71232 q = 1) (hb : d71788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4617 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71233 q = 1) (hb : d71789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71233, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71233, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71234 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71235 q = 1) (hb : d71790 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71235, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71235, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71236 q = 1) (hb : d71791 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71236, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71236, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71237 q = 1) (hb : d71792 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71237, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71237, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71238 q = 1) (hb : d71793 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71238, d71793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71238, d71793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4619 (p : Pattern) (ha : d1804 p = 1) (hb : d71239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d71201 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, d71201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1645 q = 1) (hb : d71220 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d71220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d71220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1804 q = 1) (hb : d71239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d71239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1804, d71239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4620 (p : Pattern) (ha : d1810 p = 1) (hb : d71243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1654 q = 1) (hb : d71225 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d71225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d71225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1655 q = 1) (hb : d71226 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d71226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1655, d71226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1810 q = 1) (hb : d71243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d71243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1810, d71243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4621 (p : Pattern) (ha : d6412 p = 1) (hb : d71246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro214 q ha hb
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6400 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6401 q = 1) (hb : d71230 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d71230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6401, d71230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6402 q = 1) (hb : d71231 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d71231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6402, d71231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6412 q = 1) (hb : d71246 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, d71246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6412, d71246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4622 (p : Pattern) (ha : d71252 p = 1) (hb : d71806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71221 q = 1) (hb : d71781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4615 q hb ha
  have h3 (q : Pattern) (ha : d71222 q = 1) (hb : d71782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71222, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71222, d71782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71223 q = 1) (hb : d71783 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71223, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71223, d71783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71224 q = 1) (hb : d71784 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71224, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71224, d71784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71227 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71227 q = 1) (hb : d71785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4616 q hb ha
  have h8 (q : Pattern) (ha : d71228 q = 1) (hb : d71786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71228, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71228, d71786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71229 q = 1) (hb : d71787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71229, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71229, d71787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71232 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71232 q = 1) (hb : d71788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4617 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71233 q = 1) (hb : d71789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71233, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71233, d71789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71234 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71235 q = 1) (hb : d71790 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71235, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71235, d71790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71236 q = 1) (hb : d71791 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71236, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71236, d71791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71237 q = 1) (hb : d71792 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71237, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71237, d71792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d71239 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d71239 q = 1) (hb : d71794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d71794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4619 q hb ha
  have h20 (q : Pattern) (ha : d71240 q = 1) (hb : d71795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71240, d71795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71240, d71795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d71241 q = 1) (hb : d71796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71241, d71796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d71241, d71796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d71242 q = 1) (hb : d71797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71242, d71797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71242, d71797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d71243 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d71243 q = 1) (hb : d71798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d71798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4620 q hb ha
  have h25 (q : Pattern) (ha : d71244 q = 1) (hb : d71799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71244, d71799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71244, d71799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d71245 q = 1) (hb : d71800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71245, d71800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d71245, d71800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d71246 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d71246 q = 1) (hb : d71801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4621 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d71247 q = 1) (hb : d71802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71247, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d71247, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d71248 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d71249 q = 1) (hb : d71803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71249, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d71249, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
  have h33 (q : Pattern) (ha : d71250 q = 1) (hb : d71804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71250, d71804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d71250, d71804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d71251 q = 1) (hb : d71805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71251, d71805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d71251, d71805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d71252 q = 1) (hb : d71806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71252, d71806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71252, d71806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro4623 (p : Pattern) (ha : d71259 p = 1) (hb : d71813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71246 q = 1) (hb : d71801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4621 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71247 q = 1) (hb : d71802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71247, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71247, d71802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71248 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71249 q = 1) (hb : d71803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71249, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71249, d71803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71257 q = 1) (hb : d71811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71257, d71811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71257, d71811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71258 q = 1) (hb : d71812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71258, d71812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71258, d71812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71259 q = 1) (hb : d71813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71259, d71813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71259, d71813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4624 (p : Pattern) (ha : d6524 p = 1) (hb : d71267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro238 q ha hb
    | true =>
      simp only [d1900, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6521 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6522 q = 1) (hb : d71265 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d71265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6522, d71265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6523 q = 1) (hb : d71266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d71266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6523, d71266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6524 q = 1) (hb : d71267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d71267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6524, d71267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4625 (p : Pattern) (ha : d71276 p = 1) (hb : d71824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71267 q = 1) (hb : d71819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4624 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71270 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71271 q = 1) (hb : d71820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71271, d71820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71271, d71820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71272 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71273 q = 1) (hb : d71821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71273, d71821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71273, d71821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71274 q = 1) (hb : d71822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71274, d71822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71274, d71822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71275 q = 1) (hb : d71823 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71275, d71823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71275, d71823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71276 q = 1) (hb : d71824 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71276, d71824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71276, d71824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4626 (p : Pattern) (ha : d71282 p = 1) (hb : d71830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71209 q = 1) (hb : d71770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71209, d71770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71209, d71770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4612 q ha hb
  have h2 (q : Pattern) (ha : d71210 q = 1) (hb : d71771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71210, d71771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71210, d71771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71217 q = 1) (hb : d71778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71217, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4612 q ha hb
    | true =>
      simp only [d71217, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4614 q ha hb
  have h4 (q : Pattern) (ha : d71218 q = 1) (hb : d71779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71218, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71218, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71219 q = 1) (hb : d71780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71219, d71780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71219, d71780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71253 q = 1) (hb : d71807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71253, d71807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4618 q ha hb
    | true =>
      simp only [d71253, d71807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4622 q ha hb
  have h7 (q : Pattern) (ha : d71254 q = 1) (hb : d71808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71254, d71808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71254, d71808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d71255 q = 1) (hb : d71809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71255, d71809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71255, d71809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d71256 q = 1) (hb : d71810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71256, d71810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71256, d71810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71260 q = 1) (hb : d71814 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71260, d71814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71260, d71814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4623 q ha hb
  have h11 (q : Pattern) (ha : d71261 q = 1) (hb : d71815 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71261, d71815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71261, d71815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d71262 q = 1) (hb : d71816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71262, d71816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71262, d71816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d71263 q = 1) (hb : d71817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71263, d71817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71263, d71817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d71264 q = 1) (hb : d71818 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71264, d71818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71264, d71818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71277 q = 1) (hb : d71825 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71277, d71825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71277, d71825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4625 q ha hb
  have h16 (q : Pattern) (ha : d71278 q = 1) (hb : d71826 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71278, d71826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71278, d71826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d71279 q = 1) (hb : d71827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71279, d71827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d71279, d71827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d71280 q = 1) (hb : d71828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71280, d71828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71280, d71828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d71281 q = 1) (hb : d71829 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71281, d71829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d71281, d71829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d71282 q = 1) (hb : d71830 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71282, d71830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71282, d71830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4627 (p : Pattern) (ha : d71288 p = 1) (hb : d71836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71283 q = 1) (hb : d71831 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71283, d71831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71283, d71831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4626 q ha hb
  have h2 (q : Pattern) (ha : d71284 q = 1) (hb : d71832 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71284, d71832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71284, d71832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71285 q = 1) (hb : d71833 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71285, d71833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71285, d71833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71286 q = 1) (hb : d71834 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71286, d71834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71286, d71834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71287 q = 1) (hb : d71835 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71287, d71835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71287, d71835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71288 q = 1) (hb : d71836 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71288, d71836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71288, d71836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4628 (p : Pattern) (ha : d2106 p = 1) (hb : d71295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d71293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2105 q = 1) (hb : d71294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d71294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2105, d71294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2106 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d71295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d71295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4629 (p : Pattern) (ha : d71300 p = 1) (hb : d71846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71295 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4628 q hb ha
  have h3 (q : Pattern) (ha : d71296 q = 1) (hb : d71842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71296, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71296, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71297 q = 1) (hb : d71843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71297, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71297, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71298 q = 1) (hb : d71844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71298, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71298, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71299 q = 1) (hb : d71845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71299, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71299, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71300 q = 1) (hb : d71846 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71300, d71846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71300, d71846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4630 (p : Pattern) (ha : d2116 p = 1) (hb : d71303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d71293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2105 q = 1) (hb : d71294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d71294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2105, d71294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d71303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2116, d71303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4631 (p : Pattern) (ha : d71308 p = 1) (hb : d71854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71295 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4628 q hb ha
  have h3 (q : Pattern) (ha : d71296 q = 1) (hb : d71842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71296, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71296, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71297 q = 1) (hb : d71843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71297, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71297, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71298 q = 1) (hb : d71844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71298, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71298, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71299 q = 1) (hb : d71845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71299, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71299, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71303 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4630 q hb ha
  have h9 (q : Pattern) (ha : d71304 q = 1) (hb : d71850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71304, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71304, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71305 q = 1) (hb : d71851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71305, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71305, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71306 q = 1) (hb : d71852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71306, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71306, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71307 q = 1) (hb : d71853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71307, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71307, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71308 q = 1) (hb : d71854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71308, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71308, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4632 (p : Pattern) (ha : d2129 p = 1) (hb : d71313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d71293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2128 q = 1) (hb : d71312 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d71312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d71312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2129 q = 1) (hb : d71313 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d71313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d71313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4633 (p : Pattern) (ha : d2139 p = 1) (hb : d71319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2137 q = 1) (hb : d71317 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d71317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d71317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2138 q = 1) (hb : d71318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d71318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2138, d71318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2139 q = 1) (hb : d71319 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d71319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d71319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4634 (p : Pattern) (ha : d6550 p = 1) (hb : d71324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6548 q = 1) (hb : d71322 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d71322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d71322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6549 q = 1) (hb : d71323 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d71323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6549, d71323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6550 q = 1) (hb : d71324 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d71324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d71324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4635 (p : Pattern) (ha : d71330 p = 1) (hb : d71870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71313 q = 1) (hb : d71858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4632 q hb ha
  have h3 (q : Pattern) (ha : d71314 q = 1) (hb : d71859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71314, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71314, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71315 q = 1) (hb : d71860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71315, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71315, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71316 q = 1) (hb : d71861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71316, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71316, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71319 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71319 q = 1) (hb : d71862 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4633 q hb ha
  have h8 (q : Pattern) (ha : d71320 q = 1) (hb : d71863 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71320, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71320, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71321 q = 1) (hb : d71864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71321, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71321, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71324 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71324 q = 1) (hb : d71865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4634 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71325 q = 1) (hb : d71866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71325, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71325, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71326 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71327 q = 1) (hb : d71867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71327, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71327, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71328 q = 1) (hb : d71868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71328, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71328, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71329 q = 1) (hb : d71869 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71329, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71329, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71330 q = 1) (hb : d71870 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71330, d71870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71330, d71870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4636 (p : Pattern) (ha : d2282 p = 1) (hb : d71331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d71293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, d71293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2128 q = 1) (hb : d71312 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d71312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d71312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2282 q = 1) (hb : d71331 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d71331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2282, d71331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4637 (p : Pattern) (ha : d2288 p = 1) (hb : d71335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2137 q = 1) (hb : d71317 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d71317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d71317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2138 q = 1) (hb : d71318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d71318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2138, d71318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2288 q = 1) (hb : d71335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d71335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2288, d71335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4638 (p : Pattern) (ha : d6559 p = 1) (hb : d71338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6548 q = 1) (hb : d71322 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d71322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d71322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6549 q = 1) (hb : d71323 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d71323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6549, d71323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6559 q = 1) (hb : d71338 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d71338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6559, d71338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4639 (p : Pattern) (ha : d71344 p = 1) (hb : d71883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71313 q = 1) (hb : d71858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4632 q hb ha
  have h3 (q : Pattern) (ha : d71314 q = 1) (hb : d71859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71314, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71314, d71859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71315 q = 1) (hb : d71860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71315, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71315, d71860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71316 q = 1) (hb : d71861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71316, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71316, d71861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71319 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71319 q = 1) (hb : d71862 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d71862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4633 q hb ha
  have h8 (q : Pattern) (ha : d71320 q = 1) (hb : d71863 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71320, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71320, d71863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71321 q = 1) (hb : d71864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71321, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71321, d71864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71324 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71324 q = 1) (hb : d71865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4634 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71325 q = 1) (hb : d71866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71325, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71325, d71866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71326 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71327 q = 1) (hb : d71867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71327, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71327, d71867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d71328 q = 1) (hb : d71868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71328, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71328, d71868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71329 q = 1) (hb : d71869 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71329, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71329, d71869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d71331 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d71331 q = 1) (hb : d71871 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d71871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4636 q hb ha
  have h20 (q : Pattern) (ha : d71332 q = 1) (hb : d71872 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71332, d71872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71332, d71872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d71333 q = 1) (hb : d71873 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71333, d71873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d71333, d71873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d71334 q = 1) (hb : d71874 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71334, d71874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71334, d71874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d71335 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d71335 q = 1) (hb : d71875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d71875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4637 q hb ha
  have h25 (q : Pattern) (ha : d71336 q = 1) (hb : d71876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71336, d71876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71336, d71876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d71337 q = 1) (hb : d71877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71337, d71877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d71337, d71877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d71338 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d71338 q = 1) (hb : d71878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4638 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d71339 q = 1) (hb : d71879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71339, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d71339, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d71340 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d71341 q = 1) (hb : d71880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71341, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d71341, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
  have h33 (q : Pattern) (ha : d71342 q = 1) (hb : d71881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71342, d71881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d71342, d71881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d71343 q = 1) (hb : d71882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71343, d71882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d71343, d71882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d71344 q = 1) (hb : d71883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71344, d71883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71344, d71883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro4640 (p : Pattern) (ha : d71351 p = 1) (hb : d71890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71338 q = 1) (hb : d71878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4638 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71339 q = 1) (hb : d71879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71339, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71339, d71879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71340 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71341 q = 1) (hb : d71880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71341, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71341, d71880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71349 q = 1) (hb : d71888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71349, d71888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71349, d71888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71350 q = 1) (hb : d71889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71350, d71889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71350, d71889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71351 q = 1) (hb : d71890 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71351, d71890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71351, d71890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4641 (p : Pattern) (ha : d6671 p = 1) (hb : d71359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro297 q ha hb
    | true =>
      simp only [d2378, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6668 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6669 q = 1) (hb : d71357 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d71357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6669, d71357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6670 q = 1) (hb : d71358 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d71358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6670, d71358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6671 q = 1) (hb : d71359 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d71359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6671, d71359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4642 (p : Pattern) (ha : d71368 p = 1) (hb : d71901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71359 q = 1) (hb : d71896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4641 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71362 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71363 q = 1) (hb : d71897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71363, d71897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71363, d71897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71364 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71365 q = 1) (hb : d71898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71365, d71898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71365, d71898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71366 q = 1) (hb : d71899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71366, d71899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71366, d71899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71367 q = 1) (hb : d71900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71367, d71900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71367, d71900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71368 q = 1) (hb : d71901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71368, d71901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71368, d71901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4643 (p : Pattern) (ha : d71374 p = 1) (hb : d71907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71301 q = 1) (hb : d71847 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71301, d71847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71301, d71847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4629 q ha hb
  have h2 (q : Pattern) (ha : d71302 q = 1) (hb : d71848 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71302, d71848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71302, d71848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71309 q = 1) (hb : d71855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71309, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4629 q ha hb
    | true =>
      simp only [d71309, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4631 q ha hb
  have h4 (q : Pattern) (ha : d71310 q = 1) (hb : d71856 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71310, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71310, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71311 q = 1) (hb : d71857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71311, d71857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71311, d71857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71345 q = 1) (hb : d71884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71345, d71884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4635 q ha hb
    | true =>
      simp only [d71345, d71884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4639 q ha hb
  have h7 (q : Pattern) (ha : d71346 q = 1) (hb : d71885 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71346, d71885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71346, d71885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d71347 q = 1) (hb : d71886 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71347, d71886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71347, d71886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d71348 q = 1) (hb : d71887 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71348, d71887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71348, d71887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71352 q = 1) (hb : d71891 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71352, d71891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71352, d71891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4640 q ha hb
  have h11 (q : Pattern) (ha : d71353 q = 1) (hb : d71892 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71353, d71892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71353, d71892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d71354 q = 1) (hb : d71893 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71354, d71893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71354, d71893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d71355 q = 1) (hb : d71894 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71355, d71894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71355, d71894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d71356 q = 1) (hb : d71895 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71356, d71895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71356, d71895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71369 q = 1) (hb : d71902 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71369, d71902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71369, d71902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4642 q ha hb
  have h16 (q : Pattern) (ha : d71370 q = 1) (hb : d71903 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71370, d71903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71370, d71903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d71371 q = 1) (hb : d71904 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71371, d71904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d71371, d71904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d71372 q = 1) (hb : d71905 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71372, d71905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d71372, d71905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d71373 q = 1) (hb : d71906 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71373, d71906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d71373, d71906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d71374 q = 1) (hb : d71907 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71374, d71907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71374, d71907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4644 (p : Pattern) (ha : d71380 p = 1) (hb : d71913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71375 q = 1) (hb : d71908 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71375, d71908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71375, d71908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4643 q ha hb
  have h2 (q : Pattern) (ha : d71376 q = 1) (hb : d71909 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71376, d71909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71376, d71909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71377 q = 1) (hb : d71910 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71377, d71910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71377, d71910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71378 q = 1) (hb : d71911 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71378, d71911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71378, d71911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71379 q = 1) (hb : d71912 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71379, d71912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71379, d71912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71380 q = 1) (hb : d71913 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71380, d71913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71380, d71913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4645 (p : Pattern) (ha : d71386 p = 1) (hb : d71919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d71019 q = 1) (hb : d71612 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71019, d71612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4559 q ha hb
    | true =>
      simp only [d71019, d71612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4576 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71108 q = 1) (hb : d71686 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71108, d71686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71108, d71686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4593 q ha hb
  have h3 (q : Pattern) (ha : d71109 q = 1) (hb : d71687 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71109, d71687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71109, d71687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71198 q = 1) (hb : d71761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71198, d71761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71198, d71761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4610 q ha hb
  have h5 (q : Pattern) (ha : d71199 q = 1) (hb : d71762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71199, d71762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71199, d71762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71200 q = 1) (hb : d71763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d71200, d71763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71200, d71763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71289 q = 1) (hb : d71837 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71289, d71837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71289, d71837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4627 q ha hb
  have h8 (q : Pattern) (ha : d71290 q = 1) (hb : d71838 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71290, d71838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71290, d71838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71291 q = 1) (hb : d71839 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d71291, d71839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71291, d71839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71292 q = 1) (hb : d71840 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d71292, d71840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71292, d71840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71381 q = 1) (hb : d71914 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71381, d71914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71381, d71914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4644 q ha hb
  have h12 (q : Pattern) (ha : d71382 q = 1) (hb : d71915 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71382, d71915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71382, d71915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71383 q = 1) (hb : d71916 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d71383, d71916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71383, d71916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d71384 q = 1) (hb : d71917 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d71384, d71917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71384, d71917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71385 q = 1) (hb : d71918 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d71385, d71918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71385, d71918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71386 q = 1) (hb : d71919 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d71386, d71919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71386, d71919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro4646 (p : Pattern) (ha : d71392 p = 1) (hb : d71925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71387 q = 1) (hb : d71920 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d71387, d71920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4645 q ha hb
    | true =>
      simp only [d71387, d71920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71388 q = 1) (hb : d71921 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d71388, d71921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71388, d71921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71389 q = 1) (hb : d71922 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d71389, d71922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71389, d71922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71390 q = 1) (hb : d71923 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d71390, d71923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71390, d71923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71391 q = 1) (hb : d71924 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d71391, d71924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71391, d71924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71392 q = 1) (hb : d71925 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d71392, d71925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71392, d71925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4647 (p : Pattern) (ha : d71398 p = 1) (hb : d71931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71393 q = 1) (hb : d71926 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d71393, d71926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4646 q ha hb
    | true =>
      simp only [d71393, d71926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71394 q = 1) (hb : d71927 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d71394, d71927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71394, d71927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71395 q = 1) (hb : d71928 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d71395, d71928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71395, d71928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71396 q = 1) (hb : d71929 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d71396, d71929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71396, d71929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71397 q = 1) (hb : d71930 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d71397, d71930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71397, d71930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71398 q = 1) (hb : d71931 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d71398, d71931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71398, d71931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4648 (p : Pattern) (ha : d71404 p = 1) (hb : d71937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71399 q = 1) (hb : d71932 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d71399, d71932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4647 q ha hb
    | true =>
      simp only [d71399, d71932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71400 q = 1) (hb : d71933 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d71400, d71933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71400, d71933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71401 q = 1) (hb : d71934 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d71401, d71934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71401, d71934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71402 q = 1) (hb : d71935 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d71402, d71935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71402, d71935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71403 q = 1) (hb : d71936 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d71403, d71936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71403, d71936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71404 q = 1) (hb : d71937 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d71404, d71937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71404, d71937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4649 (p : Pattern) (ha : d71410 p = 1) (hb : d71943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71405 q = 1) (hb : d71938 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d71405, d71938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4648 q ha hb
    | true =>
      simp only [d71405, d71938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71406 q = 1) (hb : d71939 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d71406, d71939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71406, d71939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71407 q = 1) (hb : d71940 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d71407, d71940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71407, d71940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71408 q = 1) (hb : d71941 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d71408, d71941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71408, d71941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71409 q = 1) (hb : d71942 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d71409, d71942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71409, d71942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71410 q = 1) (hb : d71943 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d71410, d71943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71410, d71943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4650 (p : Pattern) (ha : d71416 p = 1) (hb : d71949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71411 q = 1) (hb : d71944 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d71411, d71944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4649 q ha hb
    | true =>
      simp only [d71411, d71944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71412 q = 1) (hb : d71945 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d71412, d71945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71412, d71945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71413 q = 1) (hb : d71946 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d71413, d71946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71413, d71946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71414 q = 1) (hb : d71947 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d71414, d71947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71414, d71947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71415 q = 1) (hb : d71948 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d71415, d71948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71415, d71948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71416 q = 1) (hb : d71949 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d71416, d71949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71416, d71949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4651 (p : Pattern) (ha : d71422 p = 1) (hb : d71955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71417 q = 1) (hb : d71950 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d71417, d71950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4650 q ha hb
    | true =>
      simp only [d71417, d71950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71418 q = 1) (hb : d71951 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d71418, d71951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71418, d71951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71419 q = 1) (hb : d71952 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d71419, d71952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71419, d71952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71420 q = 1) (hb : d71953 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d71420, d71953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71420, d71953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71421 q = 1) (hb : d71954 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d71421, d71954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71421, d71954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71422 q = 1) (hb : d71955 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d71422, d71955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71422, d71955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4652 (p : Pattern) (ha : d71428 p = 1) (hb : d71961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71423 q = 1) (hb : d71956 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d71423, d71956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4651 q ha hb
    | true =>
      simp only [d71423, d71956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71424 q = 1) (hb : d71957 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d71424, d71957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71424, d71957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71425 q = 1) (hb : d71958 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d71425, d71958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71425, d71958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71426 q = 1) (hb : d71959 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d71426, d71959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71426, d71959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71427 q = 1) (hb : d71960 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d71427, d71960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71427, d71960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71428 q = 1) (hb : d71961 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d71428, d71961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71428, d71961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4653 (p : Pattern) (ha : d406 p = 1) (hb : d70147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d50, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4654 (p : Pattern) (ha : d462 p = 1) (hb : d70147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84, d70147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d458 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4655 (p : Pattern) (ha : d53647 p = 1) (hb : d70148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4456 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4457 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d70148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d70148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53637 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53638 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4653 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d70148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d70148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4654 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d70148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d70148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4656 (p : Pattern) (ha : d53655 p = 1) (hb : d70147 p = 1) : d71964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d49 q = 1) (hb : d70145 q = 1) : d49 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204 q = 1) (hb : d70147 q = 1) : d71435 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d70147, d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204, d70147, d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287 q = 1) (hb : d70147 q = 1) : d71475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288 q = 1) (hb : d70147 q = 1) : d71476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d289 q = 1) (hb : d70147 q = 1) : d71477 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290 q = 1) (hb : d70147 q = 1) : d71478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53655 q = 1) (hb : d70147 q = 1) : d71964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d71964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d71964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4657 (p : Pattern) (ha : d53665 p = 1) (hb : d70147 p = 1) : d71974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83 q = 1) (hb : d70145 q = 1) : d83 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244 q = 1) (hb : d70147 q = 1) : d71451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d70147, d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d244, d70147, d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53661 q = 1) (hb : d70147 q = 1) : d71970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d71970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d71970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53662 q = 1) (hb : d70147 q = 1) : d71971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d71971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53662, d71971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53663 q = 1) (hb : d70147 q = 1) : d71972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d71972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d71972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53664 q = 1) (hb : d70147 q = 1) : d71973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d71973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d71973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53665 q = 1) (hb : d70147 q = 1) : d71974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d71974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d71974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4658 (p : Pattern) (ha : d53671 p = 1) (hb : d70148 p = 1) : d71980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d70147 q = 1) : d71480 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d71480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4463 q ha hb
    | true =>
      simp only [d292, d71480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4464 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d70148 q = 1) : d71481 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d70148, d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d70148, d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53653 q = 1) (hb : d70148 q = 1) : d71962 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d71962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, d71962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53654 q = 1) (hb : d70148 q = 1) : d71963 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d71963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d71963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53656 q = 1) (hb : d70147 q = 1) : d71965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d71965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53656, d71965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4656 q ha hb
  have h8 (q : Pattern) (ha : d53657 q = 1) (hb : d70148 q = 1) : d71966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d70148, d71966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53657, d70148, d71966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53658 q = 1) (hb : d70148 q = 1) : d71967 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d71967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53658, d71967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53659 q = 1) (hb : d70148 q = 1) : d71968 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d71968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53659, d71968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53660 q = 1) (hb : d70148 q = 1) : d71969 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d71969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53660, d71969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53666 q = 1) (hb : d70147 q = 1) : d71975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d71975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53666, d71975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4657 q ha hb
  have h13 (q : Pattern) (ha : d53667 q = 1) (hb : d70148 q = 1) : d71976 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d70148, d71976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53667, d70148, d71976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53668 q = 1) (hb : d70148 q = 1) : d71977 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d71977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53668, d71977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53669 q = 1) (hb : d70148 q = 1) : d71978 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d71978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53669, d71978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53670 q = 1) (hb : d70148 q = 1) : d71979 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d71979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53670, d71979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53671 q = 1) (hb : d70148 q = 1) : d71980 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d71980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53671, d71980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4659 (p : Pattern) (ha : d53677 p = 1) (hb : d70148 p = 1) : d71986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4655 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d70148 q = 1) : d71981 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d71981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d71981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4658 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d70148 q = 1) : d71982 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d71982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d71982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d70148 q = 1) : d71983 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d71983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d71983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d70148 q = 1) : d71984 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d71984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d71984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d70148 q = 1) : d71985 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d71985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d71985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d70148 q = 1) : d71986 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d71986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d71986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4660 (p : Pattern) (ha : d53680 p = 1) (hb : d70147 p = 1) : d71989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d501 q = 1) (hb : d70145 q = 1) : d501 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d502 q = 1) (hb : d70147 q = 1) : d71547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d70147, d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d502, d70147, d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d503 q = 1) (hb : d70147 q = 1) : d71548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d504 q = 1) (hb : d70147 q = 1) : d71549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d504, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d505 q = 1) (hb : d70147 q = 1) : d71550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d506 q = 1) (hb : d70147 q = 1) : d71551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53680 q = 1) (hb : d70147 q = 1) : d71989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d71989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d71989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4661 (p : Pattern) (ha : d53691 p = 1) (hb : d70147 p = 1) : d72000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d730 q = 1) (hb : d70145 q = 1) : d730 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53686 q = 1) (hb : d70147 q = 1) : d71995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d70147, d71995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53686, d70147, d71995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53687 q = 1) (hb : d70147 q = 1) : d71996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d71996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d71996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53688 q = 1) (hb : d70147 q = 1) : d71997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d71997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53688, d71997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53689 q = 1) (hb : d70147 q = 1) : d71998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d71998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d71998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53690 q = 1) (hb : d70147 q = 1) : d71999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d71999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d71999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53691 q = 1) (hb : d70147 q = 1) : d72000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d72000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d72000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4662 (p : Pattern) (ha : d53697 p = 1) (hb : d70148 p = 1) : d72006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d70147 q = 1) : d71553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d71553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4474 q ha hb
    | true =>
      simp only [d508, d71553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4475 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d70148 q = 1) : d71554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d70148, d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d70148, d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53678 q = 1) (hb : d70148 q = 1) : d71987 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d71987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, d71987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53679 q = 1) (hb : d70148 q = 1) : d71988 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d71988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d71988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53681 q = 1) (hb : d70147 q = 1) : d71990 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d71990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53681, d71990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4660 q ha hb
  have h8 (q : Pattern) (ha : d53682 q = 1) (hb : d70148 q = 1) : d71991 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d70148, d71991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53682, d70148, d71991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53683 q = 1) (hb : d70148 q = 1) : d71992 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d71992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53683, d71992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53684 q = 1) (hb : d70148 q = 1) : d71993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d71993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53684, d71993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53685 q = 1) (hb : d70148 q = 1) : d71994 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d71994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53685, d71994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53692 q = 1) (hb : d70147 q = 1) : d72001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d72001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53692, d72001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4661 q ha hb
  have h13 (q : Pattern) (ha : d53693 q = 1) (hb : d70148 q = 1) : d72002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d70148, d72002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53693, d70148, d72002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53694 q = 1) (hb : d70148 q = 1) : d72003 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d72003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53694, d72003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53695 q = 1) (hb : d70148 q = 1) : d72004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d72004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53695, d72004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53696 q = 1) (hb : d70148 q = 1) : d72005 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d72005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53696, d72005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53697 q = 1) (hb : d70148 q = 1) : d72006 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d72006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53697, d72006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4663 (p : Pattern) (ha : d53703 p = 1) (hb : d70148 p = 1) : d72012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d70148 q = 1) : d72007 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d72007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d72007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4662 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d70148 q = 1) : d72008 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d72008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d72008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d70148 q = 1) : d72009 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d72009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d72009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d70148 q = 1) : d72010 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d72010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d72010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d70148 q = 1) : d72011 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d72011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d72011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d70148 q = 1) : d72012 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d72012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d72012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4664 (p : Pattern) (ha : d53707 p = 1) (hb : d70147 p = 1) : d72016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d793 q = 1) (hb : d70145 q = 1) : d793 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d794 q = 1) (hb : d70147 q = 1) : d71621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d70147, d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d794, d70147, d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d795 q = 1) (hb : d70147 q = 1) : d71622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d796 q = 1) (hb : d70147 q = 1) : d71623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d796, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d797 q = 1) (hb : d70147 q = 1) : d71624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d798 q = 1) (hb : d70147 q = 1) : d71625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53707 q = 1) (hb : d70147 q = 1) : d72016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d72016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d72016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4665 (p : Pattern) (ha : d53718 p = 1) (hb : d70147 p = 1) : d72027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1063 q = 1) (hb : d70145 q = 1) : d1063 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53713 q = 1) (hb : d70147 q = 1) : d72022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d70147, d72022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53713, d70147, d72022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53714 q = 1) (hb : d70147 q = 1) : d72023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d72023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d72023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53715 q = 1) (hb : d70147 q = 1) : d72024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d72024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53715, d72024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53716 q = 1) (hb : d70147 q = 1) : d72025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d72025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d72025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53717 q = 1) (hb : d70147 q = 1) : d72026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d72026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d72026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53718 q = 1) (hb : d70147 q = 1) : d72027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d72027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d72027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4666 (p : Pattern) (ha : d53724 p = 1) (hb : d70148 p = 1) : d72033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d70147 q = 1) : d71627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d71627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4485 q ha hb
    | true =>
      simp only [d800, d71627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4486 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d70148 q = 1) : d71628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d70148, d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d70148, d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53705 q = 1) (hb : d70148 q = 1) : d72014 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d72014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, d72014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53706 q = 1) (hb : d70148 q = 1) : d72015 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d72015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d72015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53708 q = 1) (hb : d70147 q = 1) : d72017 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d72017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53708, d72017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4664 q ha hb
  have h8 (q : Pattern) (ha : d53709 q = 1) (hb : d70148 q = 1) : d72018 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d70148, d72018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53709, d70148, d72018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53710 q = 1) (hb : d70148 q = 1) : d72019 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d72019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53710, d72019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53711 q = 1) (hb : d70148 q = 1) : d72020 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d72020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53711, d72020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53712 q = 1) (hb : d70148 q = 1) : d72021 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d72021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53712, d72021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53719 q = 1) (hb : d70147 q = 1) : d72028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d72028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53719, d72028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4665 q ha hb
  have h13 (q : Pattern) (ha : d53720 q = 1) (hb : d70148 q = 1) : d72029 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d70148, d72029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53720, d70148, d72029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53721 q = 1) (hb : d70148 q = 1) : d72030 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d72030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53721, d72030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53722 q = 1) (hb : d70148 q = 1) : d72031 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d72031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53722, d72031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53723 q = 1) (hb : d70148 q = 1) : d72032 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d72032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53723, d72032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53724 q = 1) (hb : d70148 q = 1) : d72033 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d72033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53724, d72033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4667 (p : Pattern) (ha : d53730 p = 1) (hb : d70148 p = 1) : d72039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d70148 q = 1) : d72034 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d72034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d72034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4666 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d70148 q = 1) : d72035 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d72035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d72035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d70148 q = 1) : d72036 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d72036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d72036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d70148 q = 1) : d72037 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d72037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d72037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d70148 q = 1) : d72038 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d72038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d72038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d70148 q = 1) : d72039 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d72039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d72039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4668 (p : Pattern) (ha : d53735 p = 1) (hb : d70147 p = 1) : d72044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1172 q = 1) (hb : d70145 q = 1) : d1172 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1173 q = 1) (hb : d70147 q = 1) : d71696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d70147, d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1173, d70147, d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1174 q = 1) (hb : d70147 q = 1) : d71697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1175 q = 1) (hb : d70147 q = 1) : d71698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1175, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1176 q = 1) (hb : d70147 q = 1) : d71699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1177 q = 1) (hb : d70147 q = 1) : d71700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53735 q = 1) (hb : d70147 q = 1) : d72044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d72044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d72044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4669 (p : Pattern) (ha : d53746 p = 1) (hb : d70147 p = 1) : d72055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1497 q = 1) (hb : d70145 q = 1) : d1497 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53741 q = 1) (hb : d70147 q = 1) : d72050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d70147, d72050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53741, d70147, d72050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53742 q = 1) (hb : d70147 q = 1) : d72051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d72051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d72051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53743 q = 1) (hb : d70147 q = 1) : d72052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d72052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53743, d72052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53744 q = 1) (hb : d70147 q = 1) : d72053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d72053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d72053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53745 q = 1) (hb : d70147 q = 1) : d72054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d72054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d72054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53746 q = 1) (hb : d70147 q = 1) : d72055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d72055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d72055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4670 (p : Pattern) (ha : d53752 p = 1) (hb : d70148 p = 1) : d72061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d70147 q = 1) : d71702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4496 q ha hb
    | true =>
      simp only [d1179, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4497 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d70148 q = 1) : d71703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d70148, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d70148, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53733 q = 1) (hb : d70148 q = 1) : d72042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d72042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, d72042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53734 q = 1) (hb : d70148 q = 1) : d72043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d72043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d72043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53736 q = 1) (hb : d70147 q = 1) : d72045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d72045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53736, d72045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4668 q ha hb
  have h8 (q : Pattern) (ha : d53737 q = 1) (hb : d70148 q = 1) : d72046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d70148, d72046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53737, d70148, d72046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53738 q = 1) (hb : d70148 q = 1) : d72047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d72047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53738, d72047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53739 q = 1) (hb : d70148 q = 1) : d72048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d72048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53739, d72048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53740 q = 1) (hb : d70148 q = 1) : d72049 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d72049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53740, d72049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53747 q = 1) (hb : d70147 q = 1) : d72056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d72056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53747, d72056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4669 q ha hb
  have h13 (q : Pattern) (ha : d53748 q = 1) (hb : d70148 q = 1) : d72057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d70148, d72057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53748, d70148, d72057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53749 q = 1) (hb : d70148 q = 1) : d72058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d72058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53749, d72058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53750 q = 1) (hb : d70148 q = 1) : d72059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d72059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53750, d72059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53751 q = 1) (hb : d70148 q = 1) : d72060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d72060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53751, d72060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53752 q = 1) (hb : d70148 q = 1) : d72061 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d72061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53752, d72061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4671 (p : Pattern) (ha : d53758 p = 1) (hb : d70148 p = 1) : d72067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d70148 q = 1) : d72062 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d72062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d72062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4670 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d70148 q = 1) : d72063 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d72063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d72063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d70148 q = 1) : d72064 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d72064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d72064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d70148 q = 1) : d72065 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d72065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d72065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d70148 q = 1) : d72066 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d72066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d72066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d70148 q = 1) : d72067 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d72067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d72067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4672 (p : Pattern) (ha : d53764 p = 1) (hb : d70147 p = 1) : d72073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1633 q = 1) (hb : d70145 q = 1) : d1633 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1634 q = 1) (hb : d70147 q = 1) : d71772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d70147, d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1634, d70147, d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1635 q = 1) (hb : d70147 q = 1) : d71773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1636 q = 1) (hb : d70147 q = 1) : d71774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1636, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1637 q = 1) (hb : d70147 q = 1) : d71775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1638 q = 1) (hb : d70147 q = 1) : d71776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53764 q = 1) (hb : d70147 q = 1) : d72073 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d72073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d72073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4673 (p : Pattern) (ha : d53775 p = 1) (hb : d70147 p = 1) : d72084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1974 q = 1) (hb : d70145 q = 1) : d1974 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53770 q = 1) (hb : d70147 q = 1) : d72079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d70147, d72079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53770, d70147, d72079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53771 q = 1) (hb : d70147 q = 1) : d72080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d72080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d72080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53772 q = 1) (hb : d70147 q = 1) : d72081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d72081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53772, d72081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53773 q = 1) (hb : d70147 q = 1) : d72082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d72082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d72082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53774 q = 1) (hb : d70147 q = 1) : d72083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d72083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d72083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53775 q = 1) (hb : d70147 q = 1) : d72084 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d72084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d72084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4674 (p : Pattern) (ha : d53781 p = 1) (hb : d70148 p = 1) : d72090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d70147 q = 1) : d71778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4507 q ha hb
    | true =>
      simp only [d1640, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4508 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d70148 q = 1) : d71779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d70148, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d70148, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53762 q = 1) (hb : d70148 q = 1) : d72071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d72071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, d72071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53763 q = 1) (hb : d70148 q = 1) : d72072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d72072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d72072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53765 q = 1) (hb : d70147 q = 1) : d72074 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d72074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53765, d72074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4672 q ha hb
  have h8 (q : Pattern) (ha : d53766 q = 1) (hb : d70148 q = 1) : d72075 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d70148, d72075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53766, d70148, d72075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53767 q = 1) (hb : d70148 q = 1) : d72076 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d72076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53767, d72076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53768 q = 1) (hb : d70148 q = 1) : d72077 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d72077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53768, d72077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53769 q = 1) (hb : d70148 q = 1) : d72078 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d72078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53769, d72078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53776 q = 1) (hb : d70147 q = 1) : d72085 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d72085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53776, d72085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4673 q ha hb
  have h13 (q : Pattern) (ha : d53777 q = 1) (hb : d70148 q = 1) : d72086 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d70148, d72086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53777, d70148, d72086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53778 q = 1) (hb : d70148 q = 1) : d72087 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d72087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53778, d72087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53779 q = 1) (hb : d70148 q = 1) : d72088 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d72088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53779, d72088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53780 q = 1) (hb : d70148 q = 1) : d72089 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d72089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53780, d72089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53781 q = 1) (hb : d70148 q = 1) : d72090 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d72090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53781, d72090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4675 (p : Pattern) (ha : d53787 p = 1) (hb : d70148 p = 1) : d72096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d70148 q = 1) : d72091 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d72091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d72091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4674 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d70148 q = 1) : d72092 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d72092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d72092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d70148 q = 1) : d72093 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d72093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d72093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d70148 q = 1) : d72094 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d72094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d72094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d70148 q = 1) : d72095 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d72095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d72095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d70148 q = 1) : d72096 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d72096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d72096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4676 (p : Pattern) (ha : d53794 p = 1) (hb : d70147 p = 1) : d72103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2116 q = 1) (hb : d70145 q = 1) : d2116 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2117 q = 1) (hb : d70147 q = 1) : d71849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d70147, d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2117, d70147, d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2118 q = 1) (hb : d70147 q = 1) : d71850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2119 q = 1) (hb : d70147 q = 1) : d71851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2119, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2120 q = 1) (hb : d70147 q = 1) : d71852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2121 q = 1) (hb : d70147 q = 1) : d71853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53794 q = 1) (hb : d70147 q = 1) : d72103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d72103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d72103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4677 (p : Pattern) (ha : d53805 p = 1) (hb : d70147 p = 1) : d72114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2452 q = 1) (hb : d70145 q = 1) : d2452 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53800 q = 1) (hb : d70147 q = 1) : d72109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d70147, d72109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53800, d70147, d72109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53801 q = 1) (hb : d70147 q = 1) : d72110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d72110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d72110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53802 q = 1) (hb : d70147 q = 1) : d72111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d72111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53802, d72111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53803 q = 1) (hb : d70147 q = 1) : d72112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d72112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d72112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53804 q = 1) (hb : d70147 q = 1) : d72113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d72113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d72113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53805 q = 1) (hb : d70147 q = 1) : d72114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d72114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d72114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4678 (p : Pattern) (ha : d53811 p = 1) (hb : d70148 p = 1) : d72120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d70147 q = 1) : d71855 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4518 q ha hb
    | true =>
      simp only [d2123, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4519 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d70148 q = 1) : d71856 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d70148, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d70148, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53792 q = 1) (hb : d70148 q = 1) : d72101 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d72101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, d72101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53793 q = 1) (hb : d70148 q = 1) : d72102 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d72102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d72102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53795 q = 1) (hb : d70147 q = 1) : d72104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d72104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53795, d72104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4676 q ha hb
  have h8 (q : Pattern) (ha : d53796 q = 1) (hb : d70148 q = 1) : d72105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d70148, d72105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53796, d70148, d72105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53797 q = 1) (hb : d70148 q = 1) : d72106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d72106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53797, d72106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53798 q = 1) (hb : d70148 q = 1) : d72107 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d72107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53798, d72107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53799 q = 1) (hb : d70148 q = 1) : d72108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d72108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53799, d72108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53806 q = 1) (hb : d70147 q = 1) : d72115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d72115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53806, d72115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4677 q ha hb
  have h13 (q : Pattern) (ha : d53807 q = 1) (hb : d70148 q = 1) : d72116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d70148, d72116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53807, d70148, d72116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53808 q = 1) (hb : d70148 q = 1) : d72117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d72117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53808, d72117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53809 q = 1) (hb : d70148 q = 1) : d72118 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d72118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53809, d72118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53810 q = 1) (hb : d70148 q = 1) : d72119 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d72119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53810, d72119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53811 q = 1) (hb : d70148 q = 1) : d72120 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d72120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53811, d72120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4679 (p : Pattern) (ha : d53817 p = 1) (hb : d70148 p = 1) : d72126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d70148 q = 1) : d72121 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d72121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d72121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4678 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d70148 q = 1) : d72122 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d72122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d72122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d70148 q = 1) : d72123 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d72123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d72123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d70148 q = 1) : d72124 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d72124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d72124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d70148 q = 1) : d72125 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d72125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d72125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d70148 q = 1) : d72126 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d72126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d72126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4680 (p : Pattern) (ha : d53823 p = 1) (hb : d70148 p = 1) : d72132 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d70148 q = 1) : d72013 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d72013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4659 q ha hb
    | true =>
      simp only [d53704, d72013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4663 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d70148 q = 1) : d72040 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d72040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d72040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4667 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d70148 q = 1) : d72041 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d72041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d72041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d70148 q = 1) : d72068 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d72068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d72068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4671 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d70148 q = 1) : d72069 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d72069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d72069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d70148 q = 1) : d72070 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d72070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d72070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d70148 q = 1) : d72097 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d72097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d72097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4675 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d70148 q = 1) : d72098 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d72098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d72098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d70148 q = 1) : d72099 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d72099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d72099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d70148 q = 1) : d72100 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d72100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d72100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d70148 q = 1) : d72127 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d72127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d72127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4679 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d70148 q = 1) : d72128 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d72128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d72128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d70148 q = 1) : d72129 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d72129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d72129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d70148 q = 1) : d72130 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d72130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d72130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d70148 q = 1) : d72131 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d72131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d72131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d70148 q = 1) : d72132 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d72132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d72132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4681 (p : Pattern) (ha : d53829 p = 1) (hb : d70148 p = 1) : d72138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d70148 q = 1) : d72133 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d72133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4680 q ha hb
    | true =>
      simp only [d53824, d72133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d70148 q = 1) : d72134 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d72134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d72134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d70148 q = 1) : d72135 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d72135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d72135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d70148 q = 1) : d72136 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d72136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d72136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d70148 q = 1) : d72137 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d72137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d72137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d70148 q = 1) : d72138 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d72138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d72138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4682 (p : Pattern) (ha : d53835 p = 1) (hb : d70148 p = 1) : d72144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d70148 q = 1) : d72139 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d72139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4681 q ha hb
    | true =>
      simp only [d53830, d72139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d70148 q = 1) : d72140 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d72140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d72140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d70148 q = 1) : d72141 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d72141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d72141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d70148 q = 1) : d72142 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d72142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d72142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d70148 q = 1) : d72143 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d72143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d72143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d70148 q = 1) : d72144 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d72144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d72144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4683 (p : Pattern) (ha : d53841 p = 1) (hb : d70148 p = 1) : d72150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d70148 q = 1) : d72145 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d72145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4682 q ha hb
    | true =>
      simp only [d53836, d72145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d70148 q = 1) : d72146 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d72146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d72146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d70148 q = 1) : d72147 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d72147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d72147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d70148 q = 1) : d72148 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d72148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d72148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d70148 q = 1) : d72149 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d72149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d72149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d70148 q = 1) : d72150 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d72150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d72150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4684 (p : Pattern) (ha : d53847 p = 1) (hb : d70148 p = 1) : d72156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d70148 q = 1) : d72151 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d72151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4683 q ha hb
    | true =>
      simp only [d53842, d72151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d70148 q = 1) : d72152 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d72152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d72152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d70148 q = 1) : d72153 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d72153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d72153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d70148 q = 1) : d72154 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d72154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d72154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d70148 q = 1) : d72155 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d72155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d72155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d70148 q = 1) : d72156 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d72156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d72156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4685 (p : Pattern) (ha : d53853 p = 1) (hb : d70148 p = 1) : d72162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d70148 q = 1) : d72157 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d72157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4684 q ha hb
    | true =>
      simp only [d53848, d72157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d70148 q = 1) : d72158 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d72158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d72158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d70148 q = 1) : d72159 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d72159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d72159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d70148 q = 1) : d72160 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d72160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d72160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d70148 q = 1) : d72161 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d72161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d72161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d70148 q = 1) : d72162 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d72162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d72162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4686 (p : Pattern) (ha : d53859 p = 1) (hb : d70148 p = 1) : d72168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d70148 q = 1) : d72163 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d72163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4685 q ha hb
    | true =>
      simp only [d53854, d72163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d70148 q = 1) : d72164 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d72164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d72164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d70148 q = 1) : d72165 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d72165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d72165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d70148 q = 1) : d72166 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d72166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d72166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d70148 q = 1) : d72167 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d72167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d72167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d70148 q = 1) : d72168 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d72168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d72168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4687 (p : Pattern) (ha : d53865 p = 1) (hb : d70148 p = 1) : d72174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d70148 q = 1) : d72169 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d72169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4686 q ha hb
    | true =>
      simp only [d53860, d72169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d70148 q = 1) : d72170 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d72170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d72170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d70148 q = 1) : d72171 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d72171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d72171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d70148 q = 1) : d72172 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d72172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d72172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d70148 q = 1) : d72173 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d72173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d72173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d70148 q = 1) : d72174 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d72174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d72174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4688 (p : Pattern) (ha : d70885 p = 1) (hb : d71472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70877 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70812 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4537 q hb ha
  have h6 (q : Pattern) (ha : d70881 q = 1) (hb : d71468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d70881, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70813 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70882 q = 1) (hb : d71469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70882, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70882, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d70883 q = 1) (hb : d71470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70883, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70883, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70884 q = 1) (hb : d71471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70884, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70884, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70885 q = 1) (hb : d71472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70885, d71472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70885, d71472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4689 (p : Pattern) (ha : d70898 p = 1) (hb : d71479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70812 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4537 q hb ha
  have h5 (q : Pattern) (ha : d70881 q = 1) (hb : d71468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70881, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70813 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70882 q = 1) (hb : d71469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70882, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70882, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d70883 q = 1) (hb : d71470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70883, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70883, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70884 q = 1) (hb : d71471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70884, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70884, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70889 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70892 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70818 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4539 q hb ha
  have h15 (q : Pattern) (ha : d70894 q = 1) (hb : d71475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d70894, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70819 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d70895 q = 1) (hb : d71476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70895, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70895, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d70896 q = 1) (hb : d71477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70896, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d70896, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d70897 q = 1) (hb : d71478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70897, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d70897, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70898 q = 1) (hb : d71479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70898, d71479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70898, d71479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4690 (p : Pattern) (ha : d70905 p = 1) (hb : d71964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70818 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4539 q hb ha
  have h4 (q : Pattern) (ha : d70894 q = 1) (hb : d71475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70894, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70819 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70895 q = 1) (hb : d71476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70895, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70895, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d70903 q = 1) (hb : d71477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70903, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70903, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70904 q = 1) (hb : d71478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70904, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70904, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70905 q = 1) (hb : d71964 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70905, d71964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70905, d71964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4691 (p : Pattern) (ha : d70918 p = 1) (hb : d71974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70836 q = 1) (hb : d71451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4542 q hb ha
  have h4 (q : Pattern) (ha : d70914 q = 1) (hb : d71970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70914, d71970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70914, d71970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70837 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70915 q = 1) (hb : d71971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70915, d71971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70915, d71971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d70916 q = 1) (hb : d71972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70916, d71972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70916, d71972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70917 q = 1) (hb : d71973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70917, d71973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70917, d71973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70918 q = 1) (hb : d71974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70918, d71974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70918, d71974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4692 (p : Pattern) (ha : d70924 p = 1) (hb : d71980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70867 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70899 q = 1) (hb : d71480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70899, d71480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4688 q ha hb
    | true =>
      simp only [d70899, d71480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4689 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70900 q = 1) (hb : d71481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70900, d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70900, d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d70901 q = 1) (hb : d71962 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70901, d71962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70901, d71962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d70902 q = 1) (hb : d71963 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70902, d71963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70902, d71963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70906 q = 1) (hb : d71965 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70906, d71965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70906, d71965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4690 q ha hb
  have h7 (q : Pattern) (ha : d70907 q = 1) (hb : d71966 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70907, d71966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70907, d71966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d70908 q = 1) (hb : d71967 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70908, d71967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70908, d71967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d70909 q = 1) (hb : d71968 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70909, d71968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70909, d71968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d70910 q = 1) (hb : d71969 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70910, d71969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70910, d71969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70919 q = 1) (hb : d71975 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70919, d71975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70919, d71975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4691 q ha hb
  have h12 (q : Pattern) (ha : d70920 q = 1) (hb : d71976 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70920, d71976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70920, d71976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d70921 q = 1) (hb : d71977 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70921, d71977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70921, d71977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d70922 q = 1) (hb : d71978 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70922, d71978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70922, d71978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d70923 q = 1) (hb : d71979 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70923, d71979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70923, d71979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d70924 q = 1) (hb : d71980 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70924, d71980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70924, d71980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4693 (p : Pattern) (ha : d70930 p = 1) (hb : d71986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70852 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70925 q = 1) (hb : d71981 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70925, d71981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70925, d71981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4692 q ha hb
  have h3 (q : Pattern) (ha : d70926 q = 1) (hb : d71982 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70926, d71982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70926, d71982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70927 q = 1) (hb : d71983 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70927, d71983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70927, d71983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70928 q = 1) (hb : d71984 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70928, d71984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70928, d71984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70929 q = 1) (hb : d71985 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70929, d71985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70929, d71985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70930 q = 1) (hb : d71986 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70930, d71986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70930, d71986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4694 (p : Pattern) (ha : d70968 p = 1) (hb : d71544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70962 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70933 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4560 q hb ha
  have h6 (q : Pattern) (ha : d70963 q = 1) (hb : d71540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70963, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d70963, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70964 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70965 q = 1) (hb : d71541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70965, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70965, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d70966 q = 1) (hb : d71542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70966, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70966, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70967 q = 1) (hb : d71543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70967, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70967, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70968 q = 1) (hb : d71544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70968, d71544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70968, d71544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4695 (p : Pattern) (ha : d70982 p = 1) (hb : d71552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70954 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70962 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70933 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4560 q hb ha
  have h5 (q : Pattern) (ha : d70963 q = 1) (hb : d71540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70963, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70963, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70964 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70965 q = 1) (hb : d71541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70965, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70965, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d70966 q = 1) (hb : d71542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70966, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70966, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70967 q = 1) (hb : d71543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70967, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70967, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70972 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70975 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70976 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70941 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4562 q hb ha
  have h15 (q : Pattern) (ha : d70977 q = 1) (hb : d71548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70977, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d70977, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d70978 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d70979 q = 1) (hb : d71549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70979, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70979, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d70980 q = 1) (hb : d71550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70980, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d70980, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d70981 q = 1) (hb : d71551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70981, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d70981, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70982 q = 1) (hb : d71552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70982, d71552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70982, d71552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4696 (p : Pattern) (ha : d70989 p = 1) (hb : d71989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70976 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70941 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4562 q hb ha
  have h4 (q : Pattern) (ha : d70977 q = 1) (hb : d71548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70977, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70977, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70978 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70979 q = 1) (hb : d71549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70979, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70979, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d70987 q = 1) (hb : d71550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70987, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70987, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d70988 q = 1) (hb : d71551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70988, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70988, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70989 q = 1) (hb : d71989 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70989, d71989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70989, d71989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4697 (p : Pattern) (ha : d730 p = 1) (hb : d71000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d727 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d728 q = 1) (hb : d70998 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d70998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d728, d70998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d729 q = 1) (hb : d70999 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d70999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d729, d70999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d730 q = 1) (hb : d71000 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d71000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d730, d71000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4698 (p : Pattern) (ha : d71006 p = 1) (hb : d72000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71000 q = 1) (hb : d71995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4697 q hb ha
  have h4 (q : Pattern) (ha : d71001 q = 1) (hb : d71996 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71001, d71996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71001, d71996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71002 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71003 q = 1) (hb : d71997 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71003, d71997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71003, d71997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71004 q = 1) (hb : d71998 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71004, d71998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71004, d71998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71005 q = 1) (hb : d71999 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71005, d71999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71005, d71999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71006 q = 1) (hb : d72000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71006, d72000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71006, d72000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4699 (p : Pattern) (ha : d71012 p = 1) (hb : d72006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70949 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70983 q = 1) (hb : d71553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70983, d71553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4694 q ha hb
    | true =>
      simp only [d70983, d71553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4695 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70984 q = 1) (hb : d71554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70984, d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70984, d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d70985 q = 1) (hb : d71987 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70985, d71987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70985, d71987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d70986 q = 1) (hb : d71988 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70986, d71988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70986, d71988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70990 q = 1) (hb : d71990 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70990, d71990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70990, d71990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4696 q ha hb
  have h7 (q : Pattern) (ha : d70991 q = 1) (hb : d71991 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70991, d71991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70991, d71991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d70992 q = 1) (hb : d71992 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70992, d71992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70992, d71992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d70993 q = 1) (hb : d71993 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70993, d71993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70993, d71993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d70994 q = 1) (hb : d71994 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70994, d71994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70994, d71994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71007 q = 1) (hb : d72001 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71007, d72001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71007, d72001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4698 q ha hb
  have h12 (q : Pattern) (ha : d71008 q = 1) (hb : d72002 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71008, d72002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71008, d72002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d71009 q = 1) (hb : d72003 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71009, d72003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71009, d72003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d71010 q = 1) (hb : d72004 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71010, d72004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71010, d72004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d71011 q = 1) (hb : d72005 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71011, d72005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71011, d72005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d71012 q = 1) (hb : d72006 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71012, d72006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71012, d72006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4700 (p : Pattern) (ha : d71018 p = 1) (hb : d72012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71013 q = 1) (hb : d72007 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71013, d72007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71013, d72007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4699 q ha hb
  have h2 (q : Pattern) (ha : d71014 q = 1) (hb : d72008 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71014, d72008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71014, d72008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71015 q = 1) (hb : d72009 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71015, d72009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71015, d72009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71016 q = 1) (hb : d72010 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71016, d72010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71016, d72010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71017 q = 1) (hb : d72011 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71017, d72011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71017, d72011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71018 q = 1) (hb : d72012 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71018, d72012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71018, d72012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4701 (p : Pattern) (ha : d71057 p = 1) (hb : d71618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71048 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71022 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4577 q hb ha
  have h6 (q : Pattern) (ha : d71052 q = 1) (hb : d71614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71052, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71052, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71053 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71054 q = 1) (hb : d71615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71054, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71054, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71055 q = 1) (hb : d71616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71055, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71055, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71056 q = 1) (hb : d71617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71056, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71056, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71057 q = 1) (hb : d71618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71057, d71618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71057, d71618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4702 (p : Pattern) (ha : d71071 p = 1) (hb : d71626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71022 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4577 q hb ha
  have h5 (q : Pattern) (ha : d71052 q = 1) (hb : d71614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71052, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71052, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71053 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71054 q = 1) (hb : d71615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71054, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71054, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71055 q = 1) (hb : d71616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71055, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71055, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71056 q = 1) (hb : d71617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71056, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71056, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71061 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71064 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71065 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71030 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4579 q hb ha
  have h15 (q : Pattern) (ha : d71066 q = 1) (hb : d71622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71066, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d71066, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d71067 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d71068 q = 1) (hb : d71623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71068, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71068, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d71069 q = 1) (hb : d71624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71069, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d71069, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d71070 q = 1) (hb : d71625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71070, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71070, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71071 q = 1) (hb : d71626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71071, d71626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71071, d71626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4703 (p : Pattern) (ha : d71078 p = 1) (hb : d72016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71030 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4579 q hb ha
  have h4 (q : Pattern) (ha : d71066 q = 1) (hb : d71622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71066, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71066, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71068 q = 1) (hb : d71623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71068, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71068, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71076 q = 1) (hb : d71624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71076, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71076, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71077 q = 1) (hb : d71625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71077, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71077, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71078 q = 1) (hb : d72016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71078, d72016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71078, d72016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4704 (p : Pattern) (ha : d1063 p = 1) (hb : d71089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1060 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1061 q = 1) (hb : d71087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d71087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1061, d71087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1062 q = 1) (hb : d71088 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d71088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1062, d71088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1063 q = 1) (hb : d71089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d71089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1063, d71089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4705 (p : Pattern) (ha : d71095 p = 1) (hb : d72027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71089 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71089 q = 1) (hb : d72022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d72022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4704 q hb ha
  have h4 (q : Pattern) (ha : d71090 q = 1) (hb : d72023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71090, d72023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71090, d72023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71091 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71092 q = 1) (hb : d72024 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71092, d72024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71092, d72024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71093 q = 1) (hb : d72025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71093, d72025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71093, d72025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71094 q = 1) (hb : d72026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71094, d72026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71094, d72026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71095 q = 1) (hb : d72027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71095, d72027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71095, d72027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4706 (p : Pattern) (ha : d71101 p = 1) (hb : d72033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71038 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71072 q = 1) (hb : d71627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71072, d71627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4701 q ha hb
    | true =>
      simp only [d71072, d71627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4702 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71073 q = 1) (hb : d71628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71073, d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71073, d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d71074 q = 1) (hb : d72014 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71074, d72014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71074, d72014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d71075 q = 1) (hb : d72015 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71075, d72015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71075, d72015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71079 q = 1) (hb : d72017 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71079, d72017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71079, d72017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4703 q ha hb
  have h7 (q : Pattern) (ha : d71080 q = 1) (hb : d72018 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71080, d72018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71080, d72018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d71081 q = 1) (hb : d72019 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71081, d72019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71081, d72019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d71082 q = 1) (hb : d72020 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71082, d72020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71082, d72020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d71083 q = 1) (hb : d72021 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71083, d72021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71083, d72021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71096 q = 1) (hb : d72028 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71096, d72028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71096, d72028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4705 q ha hb
  have h12 (q : Pattern) (ha : d71097 q = 1) (hb : d72029 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71097, d72029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71097, d72029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d71098 q = 1) (hb : d72030 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71098, d72030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71098, d72030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d71099 q = 1) (hb : d72031 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71099, d72031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71099, d72031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d71100 q = 1) (hb : d72032 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71100, d72032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71100, d72032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d71101 q = 1) (hb : d72033 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71101, d72033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71101, d72033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4707 (p : Pattern) (ha : d71107 p = 1) (hb : d72039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71102 q = 1) (hb : d72034 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71102, d72034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71102, d72034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4706 q ha hb
  have h2 (q : Pattern) (ha : d71103 q = 1) (hb : d72035 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71103, d72035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71103, d72035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71104 q = 1) (hb : d72036 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71104, d72036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71104, d72036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71105 q = 1) (hb : d72037 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71105, d72037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71105, d72037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71106 q = 1) (hb : d72038 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71106, d72038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71106, d72038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71107 q = 1) (hb : d72039 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71107, d72039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71107, d72039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4708 (p : Pattern) (ha : d71147 p = 1) (hb : d71693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71141 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71112 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4594 q hb ha
  have h6 (q : Pattern) (ha : d71142 q = 1) (hb : d71689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71142, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71142, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71143 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71144 q = 1) (hb : d71690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71144, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71144, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71145 q = 1) (hb : d71691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71145, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71145, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71146 q = 1) (hb : d71692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71146, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71146, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71147 q = 1) (hb : d71693 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71147, d71693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71147, d71693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4709 (p : Pattern) (ha : d71161 p = 1) (hb : d71701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71138 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71112 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4594 q hb ha
  have h5 (q : Pattern) (ha : d71142 q = 1) (hb : d71689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71142, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71142, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71143 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71144 q = 1) (hb : d71690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71144, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71144, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71145 q = 1) (hb : d71691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71145, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71145, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71146 q = 1) (hb : d71692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71146, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71146, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71151 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71155 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71120 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4596 q hb ha
  have h15 (q : Pattern) (ha : d71156 q = 1) (hb : d71697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71156, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d71156, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d71157 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d71158 q = 1) (hb : d71698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71158, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71158, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d71159 q = 1) (hb : d71699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71159, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d71159, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d71160 q = 1) (hb : d71700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71160, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71160, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71161 q = 1) (hb : d71701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71161, d71701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71161, d71701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4710 (p : Pattern) (ha : d71168 p = 1) (hb : d72044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71120 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4596 q hb ha
  have h4 (q : Pattern) (ha : d71156 q = 1) (hb : d71697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71156, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71156, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71158 q = 1) (hb : d71698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71158, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71158, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71166 q = 1) (hb : d71699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71166, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71166, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71167 q = 1) (hb : d71700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71167, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71167, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71168 q = 1) (hb : d72044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71168, d72044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71168, d72044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4711 (p : Pattern) (ha : d1497 p = 1) (hb : d71179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1494 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1495 q = 1) (hb : d71177 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d71177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1495, d71177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1496 q = 1) (hb : d71178 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d71178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1496, d71178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1497 q = 1) (hb : d71179 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d71179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1497, d71179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4712 (p : Pattern) (ha : d71185 p = 1) (hb : d72055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71179 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71179 q = 1) (hb : d72050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d72050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4711 q hb ha
  have h4 (q : Pattern) (ha : d71180 q = 1) (hb : d72051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71180, d72051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71180, d72051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71182 q = 1) (hb : d72052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71182, d72052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71182, d72052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71183 q = 1) (hb : d72053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71183, d72053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71183, d72053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71184 q = 1) (hb : d72054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71184, d72054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71184, d72054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71185 q = 1) (hb : d72055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71185, d72055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71185, d72055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4713 (p : Pattern) (ha : d71191 p = 1) (hb : d72061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71128 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71162 q = 1) (hb : d71702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71162, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4708 q ha hb
    | true =>
      simp only [d71162, d71702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4709 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71163 q = 1) (hb : d71703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71163, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71163, d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d71164 q = 1) (hb : d72042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71164, d72042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71164, d72042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d71165 q = 1) (hb : d72043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71165, d72043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71165, d72043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71169 q = 1) (hb : d72045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71169, d72045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71169, d72045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4710 q ha hb
  have h7 (q : Pattern) (ha : d71170 q = 1) (hb : d72046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71170, d72046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71170, d72046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d71171 q = 1) (hb : d72047 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71171, d72047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71171, d72047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d71172 q = 1) (hb : d72048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71172, d72048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71172, d72048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d71173 q = 1) (hb : d72049 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71173, d72049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71173, d72049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71186 q = 1) (hb : d72056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71186, d72056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71186, d72056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4712 q ha hb
  have h12 (q : Pattern) (ha : d71187 q = 1) (hb : d72057 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71187, d72057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71187, d72057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d71188 q = 1) (hb : d72058 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71188, d72058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71188, d72058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d71189 q = 1) (hb : d72059 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71189, d72059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71189, d72059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d71190 q = 1) (hb : d72060 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71190, d72060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71190, d72060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d71191 q = 1) (hb : d72061 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71191, d72061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71191, d72061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4714 (p : Pattern) (ha : d71197 p = 1) (hb : d72067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71192 q = 1) (hb : d72062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71192, d72062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71192, d72062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4713 q ha hb
  have h2 (q : Pattern) (ha : d71193 q = 1) (hb : d72063 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71193, d72063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71193, d72063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71194 q = 1) (hb : d72064 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71194, d72064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71194, d72064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71195 q = 1) (hb : d72065 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71195, d72065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71195, d72065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71196 q = 1) (hb : d72066 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71196, d72066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71196, d72066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71197 q = 1) (hb : d72067 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71197, d72067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71197, d72067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4715 (p : Pattern) (ha : d71238 p = 1) (hb : d71769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71232 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71203 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4611 q hb ha
  have h6 (q : Pattern) (ha : d71233 q = 1) (hb : d71765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71233, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71233, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71234 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71235 q = 1) (hb : d71766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71235, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71235, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71236 q = 1) (hb : d71767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71236, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71236, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71237 q = 1) (hb : d71768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71237, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71237, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71238 q = 1) (hb : d71769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71238, d71769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71238, d71769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4716 (p : Pattern) (ha : d71252 p = 1) (hb : d71777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71224 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71232 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71203 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4611 q hb ha
  have h5 (q : Pattern) (ha : d71233 q = 1) (hb : d71765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71233, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71233, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71234 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71235 q = 1) (hb : d71766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71235, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71235, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71236 q = 1) (hb : d71767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71236, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71236, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71237 q = 1) (hb : d71768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71237, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71237, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71242 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71245 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71246 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71211 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4613 q hb ha
  have h15 (q : Pattern) (ha : d71247 q = 1) (hb : d71773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71247, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d71247, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d71248 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d71249 q = 1) (hb : d71774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71249, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71249, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d71250 q = 1) (hb : d71775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71250, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d71250, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d71251 q = 1) (hb : d71776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71251, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71251, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71252 q = 1) (hb : d71777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71252, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71252, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4717 (p : Pattern) (ha : d71259 p = 1) (hb : d72073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71211 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4613 q hb ha
  have h4 (q : Pattern) (ha : d71247 q = 1) (hb : d71773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71247, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71247, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71248 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71249 q = 1) (hb : d71774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71249, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71249, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71257 q = 1) (hb : d71775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71257, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71257, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71258 q = 1) (hb : d71776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71258, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71258, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71259 q = 1) (hb : d72073 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71259, d72073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71259, d72073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4718 (p : Pattern) (ha : d1974 p = 1) (hb : d71270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1971 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1972 q = 1) (hb : d71268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d71268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1972, d71268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1973 q = 1) (hb : d71269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d71269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1973, d71269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1974 q = 1) (hb : d71270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d71270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1974, d71270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4719 (p : Pattern) (ha : d71276 p = 1) (hb : d72084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71270 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71270 q = 1) (hb : d72079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d72079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4718 q hb ha
  have h4 (q : Pattern) (ha : d71271 q = 1) (hb : d72080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71271, d72080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71271, d72080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71272 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71273 q = 1) (hb : d72081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71273, d72081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71273, d72081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71274 q = 1) (hb : d72082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71274, d72082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71274, d72082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71275 q = 1) (hb : d72083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71275, d72083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71275, d72083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71276 q = 1) (hb : d72084 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71276, d72084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71276, d72084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4720 (p : Pattern) (ha : d71282 p = 1) (hb : d72090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71219 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71253 q = 1) (hb : d71778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71253, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4715 q ha hb
    | true =>
      simp only [d71253, d71778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4716 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71254 q = 1) (hb : d71779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71254, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71254, d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d71255 q = 1) (hb : d72071 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71255, d72071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71255, d72071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d71256 q = 1) (hb : d72072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71256, d72072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71256, d72072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71260 q = 1) (hb : d72074 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71260, d72074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71260, d72074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4717 q ha hb
  have h7 (q : Pattern) (ha : d71261 q = 1) (hb : d72075 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71261, d72075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71261, d72075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d71262 q = 1) (hb : d72076 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71262, d72076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71262, d72076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d71263 q = 1) (hb : d72077 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71263, d72077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71263, d72077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d71264 q = 1) (hb : d72078 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71264, d72078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71264, d72078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71277 q = 1) (hb : d72085 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71277, d72085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71277, d72085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4719 q ha hb
  have h12 (q : Pattern) (ha : d71278 q = 1) (hb : d72086 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71278, d72086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71278, d72086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d71279 q = 1) (hb : d72087 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71279, d72087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71279, d72087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d71280 q = 1) (hb : d72088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71280, d72088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71280, d72088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d71281 q = 1) (hb : d72089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71281, d72089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71281, d72089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d71282 q = 1) (hb : d72090 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71282, d72090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71282, d72090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4721 (p : Pattern) (ha : d71288 p = 1) (hb : d72096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71283 q = 1) (hb : d72091 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71283, d72091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71283, d72091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4720 q ha hb
  have h2 (q : Pattern) (ha : d71284 q = 1) (hb : d72092 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71284, d72092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71284, d72092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71285 q = 1) (hb : d72093 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71285, d72093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71285, d72093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71286 q = 1) (hb : d72094 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71286, d72094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71286, d72094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71287 q = 1) (hb : d72095 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71287, d72095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71287, d72095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71288 q = 1) (hb : d72096 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71288, d72096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71288, d72096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4722 (p : Pattern) (ha : d71330 p = 1) (hb : d71846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71316 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71324 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71295 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4628 q hb ha
  have h6 (q : Pattern) (ha : d71325 q = 1) (hb : d71842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71325, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71325, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71326 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71327 q = 1) (hb : d71843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71327, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71327, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71328 q = 1) (hb : d71844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71328, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71328, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71329 q = 1) (hb : d71845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71329, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71329, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71330 q = 1) (hb : d71846 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71330, d71846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71330, d71846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4723 (p : Pattern) (ha : d71344 p = 1) (hb : d71854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71316 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71295 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4628 q hb ha
  have h5 (q : Pattern) (ha : d71325 q = 1) (hb : d71842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71325, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71325, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71326 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71327 q = 1) (hb : d71843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71327, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71327, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71328 q = 1) (hb : d71844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71328, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71328, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71329 q = 1) (hb : d71845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71329, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71329, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71334 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71337 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71338 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71303 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4630 q hb ha
  have h15 (q : Pattern) (ha : d71339 q = 1) (hb : d71850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71339, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d71339, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d71340 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d71341 q = 1) (hb : d71851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71341, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71341, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d71342 q = 1) (hb : d71852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71342, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d71342, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d71343 q = 1) (hb : d71853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71343, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d71343, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71344 q = 1) (hb : d71854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71344, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71344, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4724 (p : Pattern) (ha : d71351 p = 1) (hb : d72103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71303 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4630 q hb ha
  have h4 (q : Pattern) (ha : d71339 q = 1) (hb : d71850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71339, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71339, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71340 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71341 q = 1) (hb : d71851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71341, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71341, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71349 q = 1) (hb : d71852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71349, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71349, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71350 q = 1) (hb : d71853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71350, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71350, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71351 q = 1) (hb : d72103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71351, d72103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71351, d72103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4725 (p : Pattern) (ha : d2452 p = 1) (hb : d71362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2449 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2450 q = 1) (hb : d71360 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d71360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2450, d71360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2451 q = 1) (hb : d71361 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d71361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2451, d71361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2452 q = 1) (hb : d71362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d71362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2452, d71362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4726 (p : Pattern) (ha : d71368 p = 1) (hb : d72114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71362 q = 1) (hb : d72109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d72109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4725 q hb ha
  have h4 (q : Pattern) (ha : d71363 q = 1) (hb : d72110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71363, d72110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71363, d72110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71364 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71365 q = 1) (hb : d72111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71365, d72111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71365, d72111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d71366 q = 1) (hb : d72112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71366, d72112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71366, d72112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71367 q = 1) (hb : d72113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71367, d72113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71367, d72113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71368 q = 1) (hb : d72114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71368, d72114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71368, d72114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4727 (p : Pattern) (ha : d71374 p = 1) (hb : d72120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71345 q = 1) (hb : d71855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71345, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4722 q ha hb
    | true =>
      simp only [d71345, d71855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4723 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71346 q = 1) (hb : d71856 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71346, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71346, d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d71347 q = 1) (hb : d72101 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71347, d72101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71347, d72101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d71348 q = 1) (hb : d72102 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71348, d72102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71348, d72102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71352 q = 1) (hb : d72104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71352, d72104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71352, d72104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4724 q ha hb
  have h7 (q : Pattern) (ha : d71353 q = 1) (hb : d72105 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71353, d72105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71353, d72105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d71354 q = 1) (hb : d72106 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71354, d72106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71354, d72106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d71355 q = 1) (hb : d72107 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71355, d72107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71355, d72107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d71356 q = 1) (hb : d72108 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71356, d72108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71356, d72108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71369 q = 1) (hb : d72115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71369, d72115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71369, d72115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4726 q ha hb
  have h12 (q : Pattern) (ha : d71370 q = 1) (hb : d72116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71370, d72116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71370, d72116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d71371 q = 1) (hb : d72117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71371, d72117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71371, d72117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d71372 q = 1) (hb : d72118 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71372, d72118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71372, d72118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d71373 q = 1) (hb : d72119 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71373, d72119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71373, d72119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d71374 q = 1) (hb : d72120 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71374, d72120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71374, d72120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4728 (p : Pattern) (ha : d71380 p = 1) (hb : d72126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71375 q = 1) (hb : d72121 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71375, d72121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71375, d72121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4727 q ha hb
  have h2 (q : Pattern) (ha : d71376 q = 1) (hb : d72122 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71376, d72122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71376, d72122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d71377 q = 1) (hb : d72123 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71377, d72123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71377, d72123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71378 q = 1) (hb : d72124 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71378, d72124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71378, d72124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71379 q = 1) (hb : d72125 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71379, d72125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71379, d72125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71380 q = 1) (hb : d72126 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71380, d72126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71380, d72126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4729 (p : Pattern) (ha : d71386 p = 1) (hb : d72132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d71019 q = 1) (hb : d72013 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71019, d72013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4693 q ha hb
    | true =>
      simp only [d71019, d72013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4700 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71108 q = 1) (hb : d72040 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71108, d72040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71108, d72040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4707 q ha hb
  have h3 (q : Pattern) (ha : d71109 q = 1) (hb : d72041 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71109, d72041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71109, d72041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71198 q = 1) (hb : d72068 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71198, d72068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71198, d72068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4714 q ha hb
  have h5 (q : Pattern) (ha : d71199 q = 1) (hb : d72069 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71199, d72069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71199, d72069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71200 q = 1) (hb : d72070 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d71200, d72070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71200, d72070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71289 q = 1) (hb : d72097 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71289, d72097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71289, d72097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4721 q ha hb
  have h8 (q : Pattern) (ha : d71290 q = 1) (hb : d72098 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71290, d72098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71290, d72098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71291 q = 1) (hb : d72099 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d71291, d72099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71291, d72099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71292 q = 1) (hb : d72100 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d71292, d72100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71292, d72100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71381 q = 1) (hb : d72127 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d71381, d72127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71381, d72127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4728 q ha hb
  have h12 (q : Pattern) (ha : d71382 q = 1) (hb : d72128 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d71382, d72128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71382, d72128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71383 q = 1) (hb : d72129 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d71383, d72129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71383, d72129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d71384 q = 1) (hb : d72130 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d71384, d72130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71384, d72130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71385 q = 1) (hb : d72131 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d71385, d72131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71385, d72131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71386 q = 1) (hb : d72132 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d71386, d72132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71386, d72132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro4730 (p : Pattern) (ha : d71392 p = 1) (hb : d72138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71387 q = 1) (hb : d72133 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d71387, d72133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4729 q ha hb
    | true =>
      simp only [d71387, d72133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71388 q = 1) (hb : d72134 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d71388, d72134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71388, d72134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71389 q = 1) (hb : d72135 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d71389, d72135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71389, d72135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71390 q = 1) (hb : d72136 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d71390, d72136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71390, d72136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71391 q = 1) (hb : d72137 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d71391, d72137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71391, d72137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71392 q = 1) (hb : d72138 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d71392, d72138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71392, d72138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4731 (p : Pattern) (ha : d71398 p = 1) (hb : d72144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71393 q = 1) (hb : d72139 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d71393, d72139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4730 q ha hb
    | true =>
      simp only [d71393, d72139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71394 q = 1) (hb : d72140 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d71394, d72140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71394, d72140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71395 q = 1) (hb : d72141 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d71395, d72141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71395, d72141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71396 q = 1) (hb : d72142 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d71396, d72142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71396, d72142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71397 q = 1) (hb : d72143 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d71397, d72143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71397, d72143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71398 q = 1) (hb : d72144 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d71398, d72144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71398, d72144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4732 (p : Pattern) (ha : d71404 p = 1) (hb : d72150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71399 q = 1) (hb : d72145 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d71399, d72145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4731 q ha hb
    | true =>
      simp only [d71399, d72145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71400 q = 1) (hb : d72146 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d71400, d72146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71400, d72146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71401 q = 1) (hb : d72147 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d71401, d72147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71401, d72147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71402 q = 1) (hb : d72148 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d71402, d72148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71402, d72148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71403 q = 1) (hb : d72149 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d71403, d72149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71403, d72149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71404 q = 1) (hb : d72150 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d71404, d72150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71404, d72150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4733 (p : Pattern) (ha : d71410 p = 1) (hb : d72156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71405 q = 1) (hb : d72151 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d71405, d72151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4732 q ha hb
    | true =>
      simp only [d71405, d72151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71406 q = 1) (hb : d72152 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d71406, d72152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71406, d72152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71407 q = 1) (hb : d72153 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d71407, d72153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71407, d72153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71408 q = 1) (hb : d72154 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d71408, d72154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71408, d72154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71409 q = 1) (hb : d72155 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d71409, d72155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71409, d72155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71410 q = 1) (hb : d72156 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d71410, d72156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71410, d72156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4734 (p : Pattern) (ha : d71416 p = 1) (hb : d72162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71411 q = 1) (hb : d72157 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d71411, d72157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4733 q ha hb
    | true =>
      simp only [d71411, d72157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71412 q = 1) (hb : d72158 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d71412, d72158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71412, d72158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71413 q = 1) (hb : d72159 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d71413, d72159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71413, d72159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71414 q = 1) (hb : d72160 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d71414, d72160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71414, d72160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71415 q = 1) (hb : d72161 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d71415, d72161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71415, d72161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71416 q = 1) (hb : d72162 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d71416, d72162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71416, d72162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4735 (p : Pattern) (ha : d71422 p = 1) (hb : d72168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71417 q = 1) (hb : d72163 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d71417, d72163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4734 q ha hb
    | true =>
      simp only [d71417, d72163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71418 q = 1) (hb : d72164 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d71418, d72164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71418, d72164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71419 q = 1) (hb : d72165 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d71419, d72165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71419, d72165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71420 q = 1) (hb : d72166 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d71420, d72166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71420, d72166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71421 q = 1) (hb : d72167 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d71421, d72167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71421, d72167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71422 q = 1) (hb : d72168 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d71422, d72168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71422, d72168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4736 (p : Pattern) (ha : d71428 p = 1) (hb : d72174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71423 q = 1) (hb : d72169 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d71423, d72169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4735 q ha hb
    | true =>
      simp only [d71423, d72169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d71424 q = 1) (hb : d72170 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d71424, d72170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71424, d72170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71425 q = 1) (hb : d72171 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d71425, d72171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71425, d72171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d71426 q = 1) (hb : d72172 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d71426, d72172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71426, d72172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71427 q = 1) (hb : d72173 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d71427, d72173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71427, d72173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71428 q = 1) (hb : d72174 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d71428, d72174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71428, d72174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4737 (p : Pattern) (ha : d71472 p = 1) (hb : d72179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70211 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70219 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71468 q = 1) (hb : d72175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71468, d72175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71468, d72175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70152 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71469 q = 1) (hb : d72176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71469, d72176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71469, d72176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71470 q = 1) (hb : d72177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71470, d72177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71470, d72177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71471 q = 1) (hb : d72178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71471, d72178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71471, d72178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71472 q = 1) (hb : d72179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71472, d72179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71472, d72179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4738 (p : Pattern) (ha : d71479 p = 1) (hb : d72184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70211 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70216 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71468 q = 1) (hb : d72175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71468, d72175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71468, d72175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70152 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71469 q = 1) (hb : d72176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71469, d72176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71469, d72176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71470 q = 1) (hb : d72177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71470, d72177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71470, d72177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71471 q = 1) (hb : d72178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71471, d72178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71471, d72178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70234 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70235 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71475 q = 1) (hb : d72180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71475, d72180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71475, d72180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70158 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71476 q = 1) (hb : d72181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71476, d72181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71476, d72181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71477 q = 1) (hb : d72182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71477, d72182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71477, d72182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71478 q = 1) (hb : d72183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71478, d72183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71478, d72183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71479 q = 1) (hb : d72184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71479, d72184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71479, d72184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4739 (p : Pattern) (ha : d71964 p = 1) (hb : d72191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70235 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71475 q = 1) (hb : d72180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71475, d72180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71475, d72180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70158 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71476 q = 1) (hb : d72181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71476, d72181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71476, d72181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71477 q = 1) (hb : d72189 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71477, d72189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71477, d72189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71478 q = 1) (hb : d72190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71478, d72190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71478, d72190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71964 q = 1) (hb : d72191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71964, d72191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71964, d72191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4740 (p : Pattern) (ha : d71974 p = 1) (hb : d72201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70256 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71451 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71970 q = 1) (hb : d72197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71970, d72197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71970, d72197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71971 q = 1) (hb : d72198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71971, d72198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71971, d72198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71972 q = 1) (hb : d72199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71972, d72199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71972, d72199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71973 q = 1) (hb : d72200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71973, d72200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71973, d72200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71974 q = 1) (hb : d72201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71974, d72201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71974, d72201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4741 (p : Pattern) (ha : d71980 p = 1) (hb : d72207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70206 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71480 q = 1) (hb : d72185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71480, d72185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4737 q ha hb
    | true =>
      simp only [d71480, d72185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4738 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71481 q = 1) (hb : d72186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71481, d72186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71481, d72186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71962 q = 1) (hb : d72187 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71962, d72187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71962, d72187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d71963 q = 1) (hb : d72188 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71963, d72188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71963, d72188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71965 q = 1) (hb : d72192 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71965, d72192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71965, d72192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4739 q ha hb
  have h7 (q : Pattern) (ha : d71966 q = 1) (hb : d72193 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71966, d72193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71966, d72193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d71967 q = 1) (hb : d72194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71967, d72194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71967, d72194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d71968 q = 1) (hb : d72195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71968, d72195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71968, d72195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d71969 q = 1) (hb : d72196 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71969, d72196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71969, d72196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71975 q = 1) (hb : d72202 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71975, d72202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71975, d72202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4740 q ha hb
  have h12 (q : Pattern) (ha : d71976 q = 1) (hb : d72203 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71976, d72203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71976, d72203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d71977 q = 1) (hb : d72204 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71977, d72204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71977, d72204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d71978 q = 1) (hb : d72205 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71978, d72205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71978, d72205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d71979 q = 1) (hb : d72206 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71979, d72206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71979, d72206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d71980 q = 1) (hb : d72207 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71980, d72207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71980, d72207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4742 (p : Pattern) (ha : d71986 p = 1) (hb : d72213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71981 q = 1) (hb : d72208 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71981, d72208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71981, d72208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4741 q ha hb
  have h3 (q : Pattern) (ha : d71982 q = 1) (hb : d72209 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71982, d72209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71982, d72209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71983 q = 1) (hb : d72210 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71983, d72210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71983, d72210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71984 q = 1) (hb : d72211 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71984, d72211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71984, d72211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71985 q = 1) (hb : d72212 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71985, d72212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71985, d72212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71986 q = 1) (hb : d72213 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71986, d72213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71986, d72213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4743 (p : Pattern) (ha : d71544 p = 1) (hb : d72218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71540 q = 1) (hb : d72214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71540, d72214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71540, d72214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70313 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71541 q = 1) (hb : d72215 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71541, d72215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71541, d72215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71542 q = 1) (hb : d72216 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71542, d72216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71542, d72216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71543 q = 1) (hb : d72217 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71543, d72217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71543, d72217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71544 q = 1) (hb : d72218 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71544, d72218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71544, d72218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4744 (p : Pattern) (ha : d71552 p = 1) (hb : d72223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71540 q = 1) (hb : d72214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71540, d72214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71540, d72214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71541 q = 1) (hb : d72215 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71541, d72215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71541, d72215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71542 q = 1) (hb : d72216 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71542, d72216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71542, d72216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71543 q = 1) (hb : d72217 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71543, d72217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71543, d72217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70324 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70325 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71548 q = 1) (hb : d72219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71548, d72219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71548, d72219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71549 q = 1) (hb : d72220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71549, d72220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71549, d72220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71550 q = 1) (hb : d72221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71550, d72221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71550, d72221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71551 q = 1) (hb : d72222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71551, d72222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71551, d72222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71552 q = 1) (hb : d72223 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71552, d72223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71552, d72223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4745 (p : Pattern) (ha : d71989 p = 1) (hb : d72230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71548 q = 1) (hb : d72219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71548, d72219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71548, d72219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70328 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71549 q = 1) (hb : d72220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71549, d72220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71549, d72220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71550 q = 1) (hb : d72228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71550, d72228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71550, d72228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71551 q = 1) (hb : d72229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71551, d72229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71551, d72229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71989 q = 1) (hb : d72230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71989, d72230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71989, d72230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4746 (p : Pattern) (ha : d72000 p = 1) (hb : d72240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71996 q = 1) (hb : d72236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71996, d72236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71996, d72236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70355 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71997 q = 1) (hb : d72237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71997, d72237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71997, d72237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71998 q = 1) (hb : d72238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71998, d72238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71998, d72238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71999 q = 1) (hb : d72239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71999, d72239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71999, d72239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72000 q = 1) (hb : d72240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72000, d72240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72000, d72240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4747 (p : Pattern) (ha : d72006 p = 1) (hb : d72246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71553 q = 1) (hb : d72224 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71553, d72224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4743 q ha hb
    | true =>
      simp only [d71553, d72224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4744 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71554 q = 1) (hb : d72225 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71554, d72225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71554, d72225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71987 q = 1) (hb : d72226 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71987, d72226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71987, d72226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d71988 q = 1) (hb : d72227 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71988, d72227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71988, d72227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71990 q = 1) (hb : d72231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71990, d72231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71990, d72231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4745 q ha hb
  have h7 (q : Pattern) (ha : d71991 q = 1) (hb : d72232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71991, d72232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71991, d72232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d71992 q = 1) (hb : d72233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71992, d72233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71992, d72233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d71993 q = 1) (hb : d72234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71993, d72234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71993, d72234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d71994 q = 1) (hb : d72235 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71994, d72235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71994, d72235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72001 q = 1) (hb : d72241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72001, d72241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72001, d72241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4746 q ha hb
  have h12 (q : Pattern) (ha : d72002 q = 1) (hb : d72242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72002, d72242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72002, d72242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d72003 q = 1) (hb : d72243 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72003, d72243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72003, d72243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d72004 q = 1) (hb : d72244 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72004, d72244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d72004, d72244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d72005 q = 1) (hb : d72245 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72005, d72245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72005, d72245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d72006 q = 1) (hb : d72246 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72006, d72246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72006, d72246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4748 (p : Pattern) (ha : d72012 p = 1) (hb : d72252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72007 q = 1) (hb : d72247 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72007, d72247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72007, d72247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4747 q ha hb
  have h2 (q : Pattern) (ha : d72008 q = 1) (hb : d72248 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72008, d72248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72008, d72248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72009 q = 1) (hb : d72249 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72009, d72249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72009, d72249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72010 q = 1) (hb : d72250 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72010, d72250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72010, d72250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72011 q = 1) (hb : d72251 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72011, d72251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72011, d72251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72012 q = 1) (hb : d72252 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72012, d72252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72012, d72252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4749 (p : Pattern) (ha : d71618 p = 1) (hb : d72258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70396 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70404 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71614 q = 1) (hb : d72254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71614, d72254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71614, d72254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70409 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71615 q = 1) (hb : d72255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71615, d72255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71615, d72255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71616 q = 1) (hb : d72256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71616, d72256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71616, d72256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71617 q = 1) (hb : d72257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71617, d72257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71617, d72257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71618 q = 1) (hb : d72258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71618, d72258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71618, d72258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
