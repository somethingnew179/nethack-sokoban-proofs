import NetHack.Soko22Hazard87.AndIntroBlocks0096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro24250 (p : Pattern) (ha : d1327 p = 1) (hb : d135431 p = 1) : d138647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d135431 q = 1) : d138599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d135431 q = 1) : d138647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d138647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d138647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24251 (p : Pattern) (ha : d1332 p = 1) (hb : d135431 p = 1) : d138652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d135431 q = 1) : d138570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d135431 q = 1) : d138605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d135431 q = 1) : d138606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1332 q = 1) (hb : d135431 q = 1) : d138652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, d138652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1332, d138652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24252 (p : Pattern) (ha : d1333 p = 1) (hb : d135431 p = 1) : d138653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d135431 q = 1) : d138608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d135431 q = 1) : d138609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d135431 q = 1) : d138653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d138653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d138653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24253 (p : Pattern) (ha : d1337 p = 1) (hb : d135431 p = 1) : d138657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d135431 q = 1) : d138620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24244 q ha hb
    | true =>
      simp only [d1222, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d135431 q = 1) : d138621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d135431 q = 1) : d138622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d135431 q = 1) : d138623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d135431 q = 1) : d138624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1337 q = 1) (hb : d135431 q = 1) : d138657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1337, d138657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1337, d138657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24254 (p : Pattern) (ha : d5565 p = 1) (hb : d135431 p = 1) : d138660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5553 q = 1) (hb : d135431 q = 1) : d138634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5553, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24246 q ha hb
    | true =>
      simp only [d5553, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5554 q = 1) (hb : d135431 q = 1) : d138635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5554, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5554, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5555 q = 1) (hb : d135431 q = 1) : d138636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5555, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5555, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5556 q = 1) (hb : d135431 q = 1) : d138637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5556, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5556, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5557 q = 1) (hb : d135431 q = 1) : d138638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5557, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5557, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5565 q = 1) (hb : d135431 q = 1) : d138660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5565, d138660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5565, d138660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24255 (p : Pattern) (ha : d74694 p = 1) (hb : d135431 p = 1) : d138666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d135431 q = 1) : d138601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24240 q ha hb
    | true =>
      simp only [d1186, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24241 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d135431 q = 1) : d138602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d135431 q = 1) : d138603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d135431 q = 1) : d138604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d135431 q = 1) : d138611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24242 q ha hb
    | true =>
      simp only [d1196, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24243 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d135431 q = 1) : d138612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d135431 q = 1) : d138613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d135431 q = 1) : d138626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24245 q ha hb
    | true =>
      simp only [d1228, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24228 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d135431 q = 1) : d138627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5559 q = 1) (hb : d135431 q = 1) : d138640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5559, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24247 q ha hb
    | true =>
      simp only [d5559, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5560 q = 1) (hb : d135431 q = 1) : d138641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5560, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5560, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74687 q = 1) (hb : d135431 q = 1) : d138642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74687, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74688 q = 1) (hb : d135431 q = 1) : d138643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74688, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74689 q = 1) (hb : d135431 q = 1) : d138644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74689, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1328 q = 1) (hb : d135431 q = 1) : d138648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d138648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24249 q ha hb
    | true =>
      simp only [d1328, d138648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24250 q ha hb
  have h16 (q : Pattern) (ha : d1329 q = 1) (hb : d135431 q = 1) : d138649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d138649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d138649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1330 q = 1) (hb : d135431 q = 1) : d138650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d138650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1330, d138650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1331 q = 1) (hb : d135431 q = 1) : d138651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d138651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d138651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1334 q = 1) (hb : d135431 q = 1) : d138654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d138654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24251 q ha hb
    | true =>
      simp only [d1334, d138654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24252 q ha hb
  have h20 (q : Pattern) (ha : d1335 q = 1) (hb : d135431 q = 1) : d138655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d138655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d138655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1336 q = 1) (hb : d135431 q = 1) : d138656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d138656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1336, d138656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d1338 q = 1) (hb : d135431 q = 1) : d138658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24253 q ha hb
    | true =>
      simp only [d1338, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24231 q ha hb
  have h23 (q : Pattern) (ha : d4490 q = 1) (hb : d135431 q = 1) : d138659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4490, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5566 q = 1) (hb : d135431 q = 1) : d138661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5566, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24254 q ha hb
    | true =>
      simp only [d5566, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5567 q = 1) (hb : d135431 q = 1) : d138662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5567, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5567, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74691 q = 1) (hb : d135431 q = 1) : d138663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74691, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74692 q = 1) (hb : d135431 q = 1) : d138664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74692, d138664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74692, d138664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74693 q = 1) (hb : d135431 q = 1) : d138665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74693, d138665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74693, d138665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74694 q = 1) (hb : d135431 q = 1) : d138666 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74694, d138666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74694, d138666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24256 (p : Pattern) (ha : d74701 p = 1) (hb : d135431 p = 1) : d138686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1338 q = 1) (hb : d135431 q = 1) : d138658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24253 q ha hb
    | true =>
      simp only [d1338, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24231 q ha hb
  have h2 (q : Pattern) (ha : d4490 q = 1) (hb : d135431 q = 1) : d138659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4490, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5566 q = 1) (hb : d135431 q = 1) : d138661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5566, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24254 q ha hb
    | true =>
      simp only [d5566, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5567 q = 1) (hb : d135431 q = 1) : d138662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5567, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5567, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74691 q = 1) (hb : d135431 q = 1) : d138663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74691, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74699 q = 1) (hb : d135431 q = 1) : d138684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74699, d138684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74699, d138684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74700 q = 1) (hb : d135431 q = 1) : d138685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74700, d138685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74700, d138685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74701 q = 1) (hb : d135431 q = 1) : d138686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d138686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74701, d138686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24257 (p : Pattern) (ha : d1417 p = 1) (hb : d135431 p = 1) : d138706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1390 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1397 q = 1) (hb : d135431 q = 1) : d138694 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d135431, d138694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1397, d135431, d138694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
  have h3 (q : Pattern) (ha : d1398 q = 1) (hb : d135431 q = 1) : d138695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d138695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d138695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1399 q = 1) (hb : d135431 q = 1) : d138696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d138696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d138696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1396 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1402 q = 1) (hb : d135431 q = 1) : d138697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1402, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
  have h7 (q : Pattern) (ha : d1403 q = 1) (hb : d135431 q = 1) : d138698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1404 q = 1) (hb : d135431 q = 1) : d138699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1405 q = 1) (hb : d135431 q = 1) : d138700 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d138700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1405, d138700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1412 q = 1) (hb : d135431 q = 1) : d138701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h12 (q : Pattern) (ha : d1413 q = 1) (hb : d135431 q = 1) : d138702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1414 q = 1) (hb : d135431 q = 1) : d138703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1415 q = 1) (hb : d135431 q = 1) : d138704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1415, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1416 q = 1) (hb : d135431 q = 1) : d138705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d138705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1416, d138705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1417 q = 1) (hb : d135431 q = 1) : d138706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d138706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1417, d138706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro24258 (p : Pattern) (ha : d1422 p = 1) (hb : d135431 p = 1) : d138711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1396 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1402 q = 1) (hb : d135431 q = 1) : d138697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
  have h3 (q : Pattern) (ha : d1403 q = 1) (hb : d135431 q = 1) : d138698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1404 q = 1) (hb : d135431 q = 1) : d138699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1412 q = 1) (hb : d135431 q = 1) : d138701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h7 (q : Pattern) (ha : d1413 q = 1) (hb : d135431 q = 1) : d138702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1414 q = 1) (hb : d135431 q = 1) : d138703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1415 q = 1) (hb : d135431 q = 1) : d138704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1415, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1420 q = 1) (hb : d135431 q = 1) : d138709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1420, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1421 q = 1) (hb : d135431 q = 1) : d138710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d138710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1421, d138710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1422 q = 1) (hb : d135431 q = 1) : d138711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d138711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1422, d138711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro24259 (p : Pattern) (ha : d1428 p = 1) (hb : d135431 p = 1) : d138717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d135431 q = 1) : d138707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d138707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24257 q ha hb
    | true =>
      simp only [d1418, d138707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d135431 q = 1) : d138708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d138708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d138708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1423 q = 1) (hb : d135431 q = 1) : d138712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24258 q ha hb
    | true =>
      simp only [d1423, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1424 q = 1) (hb : d135431 q = 1) : d138713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1425 q = 1) (hb : d135431 q = 1) : d138714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1425, d138714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1425, d138714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1426 q = 1) (hb : d135431 q = 1) : d138715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1426, d138715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1426, d138715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1427 q = 1) (hb : d135431 q = 1) : d138716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1427, d138716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1427, d138716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1428 q = 1) (hb : d135431 q = 1) : d138717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1428, d138717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1428, d138717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24260 (p : Pattern) (ha : d1436 p = 1) (hb : d135431 p = 1) : d138725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d135431 q = 1) : d138712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24258 q ha hb
    | true =>
      simp only [d1423, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d135431 q = 1) : d138713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d135431 q = 1) : d138720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24237 q ha hb
    | true =>
      simp only [d1431, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d135431 q = 1) : d138721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1433 q = 1) (hb : d135431 q = 1) : d138722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d138722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, d138722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1434 q = 1) (hb : d135431 q = 1) : d138723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d138723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1434, d138723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1435 q = 1) (hb : d135431 q = 1) : d138724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d138724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1435, d138724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1436 q = 1) (hb : d135431 q = 1) : d138725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d138725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1436, d138725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24261 (p : Pattern) (ha : d5596 p = 1) (hb : d135431 p = 1) : d138733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1396 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1402 q = 1) (hb : d135431 q = 1) : d138697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
  have h3 (q : Pattern) (ha : d1403 q = 1) (hb : d135431 q = 1) : d138698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1404 q = 1) (hb : d135431 q = 1) : d138699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1412 q = 1) (hb : d135431 q = 1) : d138701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h7 (q : Pattern) (ha : d1413 q = 1) (hb : d135431 q = 1) : d138702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1414 q = 1) (hb : d135431 q = 1) : d138703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1415 q = 1) (hb : d135431 q = 1) : d138704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1415, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5589 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5590 q = 1) (hb : d94753 q = 1) : d5590 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5591 q = 1) (hb : d135431 q = 1) : d138728 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5591, d135431, d138728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d5591, d135431, d138728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5592 q = 1) (hb : d135431 q = 1) : d138729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5592, d138729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5592, d138729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5593 q = 1) (hb : d135431 q = 1) : d138730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5593, d138730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5593, d138730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5594 q = 1) (hb : d135431 q = 1) : d138731 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5594, d138731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5594, d138731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5595 q = 1) (hb : d135431 q = 1) : d138732 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5595, d138732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5595, d138732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5596 q = 1) (hb : d135431 q = 1) : d138733 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5596, d138733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5596, d138733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24262 (p : Pattern) (ha : d5602 p = 1) (hb : d135431 p = 1) : d138739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5597 q = 1) (hb : d135431 q = 1) : d138734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5597, d138734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24261 q ha hb
    | true =>
      simp only [d5597, d138734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5598 q = 1) (hb : d135431 q = 1) : d138735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5598, d138735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5598, d138735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5599 q = 1) (hb : d135431 q = 1) : d138736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5599, d138736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5599, d138736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5600 q = 1) (hb : d135431 q = 1) : d138737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5600, d138737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5600, d138737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5601 q = 1) (hb : d135431 q = 1) : d138738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5601, d138738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5601, d138738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5602 q = 1) (hb : d135431 q = 1) : d138739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5602, d138739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5602, d138739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24263 (p : Pattern) (ha : d74710 p = 1) (hb : d135431 p = 1) : d138745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1437 q = 1) (hb : d135431 q = 1) : d138726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d138726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24259 q ha hb
    | true =>
      simp only [d1437, d138726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24260 q ha hb
  have h2 (q : Pattern) (ha : d4505 q = 1) (hb : d135431 q = 1) : d138727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d138727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4505, d138727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5603 q = 1) (hb : d135431 q = 1) : d138740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5603, d138740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24262 q ha hb
    | true =>
      simp only [d5603, d138740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5604 q = 1) (hb : d135431 q = 1) : d138741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5604, d138741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5604, d138741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74707 q = 1) (hb : d135431 q = 1) : d138742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74707, d138742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74707, d138742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74708 q = 1) (hb : d135431 q = 1) : d138743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d138743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74708, d138743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74709 q = 1) (hb : d135431 q = 1) : d138744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d138744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74709, d138744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74710 q = 1) (hb : d135431 q = 1) : d138745 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d138745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74710, d138745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24264 (p : Pattern) (ha : d74716 p = 1) (hb : d135431 p = 1) : d138762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d135431 q = 1) : d138584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d138584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d138584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24230 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d135431 q = 1) : d138585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d138585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d138585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d135431 q = 1) : d138594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24230 q ha hb
    | true =>
      simp only [d1179, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24233 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d135431 q = 1) : d138595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d135431 q = 1) : d138596 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d138596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d138596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74695 q = 1) (hb : d135431 q = 1) : d138667 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74695, d138667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24248 q ha hb
    | true =>
      simp only [d74695, d138667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24255 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d135431 q = 1) : d138680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d138680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24234 q ha hb
    | true =>
      simp only [d1362, d138680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24235 q ha hb
  have h8 (q : Pattern) (ha : d74696 q = 1) (hb : d135431 q = 1) : d138681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74696, d138681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74696, d138681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74697 q = 1) (hb : d135431 q = 1) : d138682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d138682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74697, d138682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74698 q = 1) (hb : d135431 q = 1) : d138683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d138683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74698, d138683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74702 q = 1) (hb : d135431 q = 1) : d138687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d138687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74702, d138687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24256 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d135431 q = 1) : d138689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d138689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d138689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24236 q ha hb
  have h13 (q : Pattern) (ha : d74703 q = 1) (hb : d135431 q = 1) : d138690 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d138690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74703, d138690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74704 q = 1) (hb : d135431 q = 1) : d138691 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d138691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74704, d138691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74705 q = 1) (hb : d135431 q = 1) : d138692 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d138692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74705, d138692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74706 q = 1) (hb : d135431 q = 1) : d138693 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d138693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74706, d138693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74711 q = 1) (hb : d135431 q = 1) : d138746 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d138746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74711, d138746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24263 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d135431 q = 1) : d138757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d138757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d138757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24239 q ha hb
  have h19 (q : Pattern) (ha : d74712 q = 1) (hb : d135431 q = 1) : d138758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d138758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74712, d138758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74713 q = 1) (hb : d135431 q = 1) : d138759 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d138759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74713, d138759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74714 q = 1) (hb : d135431 q = 1) : d138760 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d138760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74714, d138760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74715 q = 1) (hb : d135431 q = 1) : d138761 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d138761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74715, d138761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74716 q = 1) (hb : d135431 q = 1) : d138762 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d138762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74716, d138762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24265 (p : Pattern) (ha : d74722 p = 1) (hb : d135431 p = 1) : d138768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74717 q = 1) (hb : d135431 q = 1) : d138763 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d138763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74717, d138763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24264 q ha hb
  have h2 (q : Pattern) (ha : d74718 q = 1) (hb : d135431 q = 1) : d138764 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d138764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74718, d138764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74719 q = 1) (hb : d135431 q = 1) : d138765 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d138765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74719, d138765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74720 q = 1) (hb : d135431 q = 1) : d138766 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d138766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74720, d138766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74721 q = 1) (hb : d135431 q = 1) : d138767 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d138767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74721, d138767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74722 q = 1) (hb : d135431 q = 1) : d138768 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d138768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74722, d138768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24266 (p : Pattern) (ha : d1609 p = 1) (hb : d135431 p = 1) : d138781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1587 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1590 q = 1) (hb : d135431 q = 1) : d138772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
  have h3 (q : Pattern) (ha : d1591 q = 1) (hb : d135431 q = 1) : d138773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1592 q = 1) (hb : d135431 q = 1) : d138774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1603 q = 1) (hb : d135431 q = 1) : d138775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h7 (q : Pattern) (ha : d1604 q = 1) (hb : d135431 q = 1) : d138776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1605 q = 1) (hb : d135431 q = 1) : d138777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1606 q = 1) (hb : d135431 q = 1) : d138778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1606, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1607 q = 1) (hb : d135431 q = 1) : d138779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1607, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1608 q = 1) (hb : d135431 q = 1) : d138780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d138780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1608, d138780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1609 q = 1) (hb : d135431 q = 1) : d138781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d138781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1609, d138781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro24267 (p : Pattern) (ha : d1613 p = 1) (hb : d135431 p = 1) : d138785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1603 q = 1) (hb : d135431 q = 1) : d138775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h3 (q : Pattern) (ha : d1604 q = 1) (hb : d135431 q = 1) : d138776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1605 q = 1) (hb : d135431 q = 1) : d138777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1607 q = 1) (hb : d135431 q = 1) : d138779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1607, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1612 q = 1) (hb : d135431 q = 1) : d138784 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d138784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1612, d138784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1613 q = 1) (hb : d135431 q = 1) : d138785 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d138785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1613, d138785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24268 (p : Pattern) (ha : d1619 p = 1) (hb : d135431 p = 1) : d138791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d135431 q = 1) : d138788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d135431 q = 1) : d138789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d135431 q = 1) : d138790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1619 q = 1) (hb : d135431 q = 1) : d138791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d138791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d138791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24269 (p : Pattern) (ha : d1623 p = 1) (hb : d135431 p = 1) : d138795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d135431 q = 1) : d138794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d135431 q = 1) : d138795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d138795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d138795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24270 (p : Pattern) (ha : d1629 p = 1) (hb : d135431 p = 1) : d138801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d135431 q = 1) : d138796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24268 q ha hb
    | true =>
      simp only [d1624, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24269 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d135431 q = 1) : d138797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d135431 q = 1) : d138798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d135431 q = 1) : d138799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d135431 q = 1) : d138800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1629 q = 1) (hb : d135431 q = 1) : d138801 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d138801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d138801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24271 (p : Pattern) (ha : d1632 p = 1) (hb : d135431 p = 1) : d138804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d135431 q = 1) : d138788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d135431 q = 1) : d138789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d135431 q = 1) : d138790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1632 q = 1) (hb : d135431 q = 1) : d138804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d138804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1632, d138804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24272 (p : Pattern) (ha : d1633 p = 1) (hb : d135431 p = 1) : d138805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d135431 q = 1) : d138794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d135431 q = 1) : d138805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d138805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d138805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24273 (p : Pattern) (ha : d1639 p = 1) (hb : d135431 p = 1) : d138811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d135431 q = 1) : d138796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24268 q ha hb
    | true =>
      simp only [d1624, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24269 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d135431 q = 1) : d138797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d135431 q = 1) : d138798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d135431 q = 1) : d138799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d135431 q = 1) : d138800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1634 q = 1) (hb : d135431 q = 1) : d138806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24271 q ha hb
    | true =>
      simp only [d1634, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24272 q ha hb
  have h7 (q : Pattern) (ha : d1635 q = 1) (hb : d135431 q = 1) : d138807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1636 q = 1) (hb : d135431 q = 1) : d138808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1636, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1637 q = 1) (hb : d135431 q = 1) : d138809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1638 q = 1) (hb : d135431 q = 1) : d138810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1639 q = 1) (hb : d135431 q = 1) : d138811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d138811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1639, d138811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24274 (p : Pattern) (ha : d1832 p = 1) (hb : d135431 p = 1) : d138891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d135431 q = 1) : d138796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24268 q ha hb
    | true =>
      simp only [d1624, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24269 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d135431 q = 1) : d138797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d135431 q = 1) : d138798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d135431 q = 1) : d138799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d135431 q = 1) : d138800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d135431 q = 1) : d138886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24269 q ha hb
    | true =>
      simp only [d1827, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d135431 q = 1) : d138887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d135431 q = 1) : d138888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d135431 q = 1) : d138889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d135431 q = 1) : d138890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1832 q = 1) (hb : d135431 q = 1) : d138891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, d138891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1832, d138891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24275 (p : Pattern) (ha : d1838 p = 1) (hb : d135431 p = 1) : d138897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d135431 q = 1) : d138886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24269 q ha hb
    | true =>
      simp only [d1827, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d135431 q = 1) : d138887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d135431 q = 1) : d138888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d135431 q = 1) : d138889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d135431 q = 1) : d138890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d135431 q = 1) : d138892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24272 q ha hb
    | true =>
      simp only [d1833, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d135431 q = 1) : d138893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d135431 q = 1) : d138894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d135431 q = 1) : d138895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d135431 q = 1) : d138896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d135431 q = 1) : d138897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d138897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d138897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24276 (p : Pattern) (ha : d1847 p = 1) (hb : d135431 p = 1) : d138906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d135431 q = 1) : d138892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24272 q ha hb
    | true =>
      simp only [d1833, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d135431 q = 1) : d138893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d135431 q = 1) : d138894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d135431 q = 1) : d138895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d135431 q = 1) : d138896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d135431 q = 1) : d138906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d138906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d138906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24277 (p : Pattern) (ha : d1907 p = 1) (hb : d135431 p = 1) : d138937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1889 q = 1) (hb : d135431 q = 1) : d138919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h3 (q : Pattern) (ha : d1890 q = 1) (hb : d135431 q = 1) : d138920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1891 q = 1) (hb : d135431 q = 1) : d138921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1897 q = 1) (hb : d135431 q = 1) : d138927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1897, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1906 q = 1) (hb : d135431 q = 1) : d138936 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d138936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1906, d138936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1907 q = 1) (hb : d135431 q = 1) : d138937 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d138937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1907, d138937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24278 (p : Pattern) (ha : d1974 p = 1) (hb : d135431 p = 1) : d138968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d135431 q = 1) : d138938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24277 q ha hb
    | true =>
      simp only [d1908, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d135431 q = 1) : d138939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d135431 q = 1) : d138965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d138965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d138965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d135431 q = 1) : d138966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d138966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d138966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d135431 q = 1) : d138967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d138967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d138967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d135431 q = 1) : d138968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d138968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d138968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24279 (p : Pattern) (ha : d1980 p = 1) (hb : d135431 p = 1) : d138974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d135431 q = 1) : d138969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d138969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24278 q ha hb
    | true =>
      simp only [d1975, d138969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d135431 q = 1) : d138970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d138970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d138970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d135431 q = 1) : d138971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d138971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d138971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d135431 q = 1) : d138972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d138972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d138972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d135431 q = 1) : d138973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d138973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d138973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d135431 q = 1) : d138974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d138974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d138974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24280 (p : Pattern) (ha : d1644 p = 1) (hb : d135431 p = 1) : d138816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d135431 q = 1) : d138788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d135431 q = 1) : d138789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d135431 q = 1) : d138815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1644 q = 1) (hb : d135431 q = 1) : d138816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d138816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d138816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24281 (p : Pattern) (ha : d1646 p = 1) (hb : d135431 p = 1) : d138818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d135431 q = 1) : d138817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d135431 q = 1) : d138818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d138818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d138818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24282 (p : Pattern) (ha : d1653 p = 1) (hb : d135431 p = 1) : d138825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d135431 q = 1) : d138788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d135431 q = 1) : d138823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d135431 q = 1) : d138824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1653 q = 1) (hb : d135431 q = 1) : d138825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d138825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d138825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24283 (p : Pattern) (ha : d1656 p = 1) (hb : d135431 p = 1) : d138828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d135431 q = 1) : d138826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d135431 q = 1) : d138827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d135431 q = 1) : d138828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d138828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d138828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24284 (p : Pattern) (ha : d1676 p = 1) (hb : d135431 p = 1) : d138837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1671 q = 1) (hb : d135431 q = 1) : d138832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d135431, d138832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1671, d135431, d138832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
  have h3 (q : Pattern) (ha : d1672 q = 1) (hb : d135431 q = 1) : d138833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d138833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d138833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1673 q = 1) (hb : d135431 q = 1) : d138834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d138834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d138834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1590 q = 1) (hb : d135431 q = 1) : d138772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1590, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
  have h7 (q : Pattern) (ha : d1591 q = 1) (hb : d135431 q = 1) : d138773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1592 q = 1) (hb : d135431 q = 1) : d138774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1674 q = 1) (hb : d135431 q = 1) : d138835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d138835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1674, d138835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1603 q = 1) (hb : d135431 q = 1) : d138775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h12 (q : Pattern) (ha : d1604 q = 1) (hb : d135431 q = 1) : d138776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1605 q = 1) (hb : d135431 q = 1) : d138777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1606 q = 1) (hb : d135431 q = 1) : d138778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1606, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1675 q = 1) (hb : d135431 q = 1) : d138836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d138836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1675, d138836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1676 q = 1) (hb : d135431 q = 1) : d138837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d138837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1676, d138837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro24285 (p : Pattern) (ha : d1682 p = 1) (hb : d135431 p = 1) : d138843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d135431 q = 1) : d138838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24284 q ha hb
    | true =>
      simp only [d1677, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d135431 q = 1) : d138839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d135431 q = 1) : d138840 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d135431 q = 1) : d138841 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d135431 q = 1) : d138842 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1682 q = 1) (hb : d135431 q = 1) : d138843 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d138843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d138843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24286 (p : Pattern) (ha : d5642 p = 1) (hb : d135431 p = 1) : d138851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1587 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1590 q = 1) (hb : d135431 q = 1) : d138772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
  have h3 (q : Pattern) (ha : d1591 q = 1) (hb : d135431 q = 1) : d138773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1592 q = 1) (hb : d135431 q = 1) : d138774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1603 q = 1) (hb : d135431 q = 1) : d138775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1603, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h7 (q : Pattern) (ha : d1604 q = 1) (hb : d135431 q = 1) : d138776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1605 q = 1) (hb : d135431 q = 1) : d138777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1606 q = 1) (hb : d135431 q = 1) : d138778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1606, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5635 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5636 q = 1) (hb : d94753 q = 1) : d5636 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5637 q = 1) (hb : d135431 q = 1) : d138846 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5637, d135431, d138846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d5637, d135431, d138846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5638 q = 1) (hb : d135431 q = 1) : d138847 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5638, d138847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5638, d138847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5639 q = 1) (hb : d135431 q = 1) : d138848 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5639, d138848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5639, d138848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5640 q = 1) (hb : d135431 q = 1) : d138849 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5640, d138849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5640, d138849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5641 q = 1) (hb : d135431 q = 1) : d138850 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5641, d138850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5641, d138850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5642 q = 1) (hb : d135431 q = 1) : d138851 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5642, d138851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5642, d138851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24287 (p : Pattern) (ha : d5648 p = 1) (hb : d135431 p = 1) : d138857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5643 q = 1) (hb : d135431 q = 1) : d138852 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5643, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24286 q ha hb
    | true =>
      simp only [d5643, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5644 q = 1) (hb : d135431 q = 1) : d138853 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5644, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5644, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5645 q = 1) (hb : d135431 q = 1) : d138854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5645, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5645, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5646 q = 1) (hb : d135431 q = 1) : d138855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5646, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5646, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5647 q = 1) (hb : d135431 q = 1) : d138856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5647, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5647, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5648 q = 1) (hb : d135431 q = 1) : d138857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5648, d138857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5648, d138857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24288 (p : Pattern) (ha : d74729 p = 1) (hb : d135431 p = 1) : d138863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d135431 q = 1) : d138819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24280 q ha hb
    | true =>
      simp only [d1647, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24281 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d135431 q = 1) : d138820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d135431 q = 1) : d138821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d135431 q = 1) : d138822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d135431 q = 1) : d138829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24282 q ha hb
    | true =>
      simp only [d1657, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24283 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d135431 q = 1) : d138830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d135431 q = 1) : d138831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d135431 q = 1) : d138844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24285 q ha hb
    | true =>
      simp only [d1683, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24268 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d135431 q = 1) : d138845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5649 q = 1) (hb : d135431 q = 1) : d138858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5649, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24287 q ha hb
    | true =>
      simp only [d5649, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5650 q = 1) (hb : d135431 q = 1) : d138859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5650, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5650, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74726 q = 1) (hb : d135431 q = 1) : d138860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74726, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74727 q = 1) (hb : d135431 q = 1) : d138861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74727, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74728 q = 1) (hb : d135431 q = 1) : d138862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74728, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74729 q = 1) (hb : d135431 q = 1) : d138863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74729, d138863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74729, d138863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24289 (p : Pattern) (ha : d1803 p = 1) (hb : d135431 p = 1) : d138864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d135431 q = 1) : d138788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d135431 q = 1) : d138789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d135431 q = 1) : d138815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1803 q = 1) (hb : d135431 q = 1) : d138864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, d138864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1803, d138864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24290 (p : Pattern) (ha : d1804 p = 1) (hb : d135431 p = 1) : d138865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d135431 q = 1) : d138817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d135431 q = 1) : d138865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d138865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d138865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24291 (p : Pattern) (ha : d1809 p = 1) (hb : d135431 p = 1) : d138870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d135431 q = 1) : d138788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d135431 q = 1) : d138823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d135431 q = 1) : d138824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1809 q = 1) (hb : d135431 q = 1) : d138870 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, d138870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1809, d138870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24292 (p : Pattern) (ha : d1810 p = 1) (hb : d135431 p = 1) : d138871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24267 q ha hb
    | true =>
      simp only [d1614, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d135431 q = 1) : d138826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d135431 q = 1) : d138827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d135431 q = 1) : d138871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d138871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d138871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24293 (p : Pattern) (ha : d1814 p = 1) (hb : d135431 p = 1) : d138875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d135431 q = 1) : d138838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24284 q ha hb
    | true =>
      simp only [d1677, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d135431 q = 1) : d138839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d135431 q = 1) : d138782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24266 q ha hb
    | true =>
      simp only [d1610, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d135431 q = 1) : d138783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d135431 q = 1) : d138840 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d135431 q = 1) : d138841 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d135431 q = 1) : d138842 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1814 q = 1) (hb : d135431 q = 1) : d138875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1814, d138875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1814, d138875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24294 (p : Pattern) (ha : d5655 p = 1) (hb : d135431 p = 1) : d138878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5643 q = 1) (hb : d135431 q = 1) : d138852 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5643, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24286 q ha hb
    | true =>
      simp only [d5643, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5644 q = 1) (hb : d135431 q = 1) : d138853 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5644, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5644, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5645 q = 1) (hb : d135431 q = 1) : d138854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5645, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5645, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5646 q = 1) (hb : d135431 q = 1) : d138855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5646, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5646, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5647 q = 1) (hb : d135431 q = 1) : d138856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5647, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5647, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5655 q = 1) (hb : d135431 q = 1) : d138878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5655, d138878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5655, d138878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24295 (p : Pattern) (ha : d74733 p = 1) (hb : d135431 p = 1) : d138884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d135431 q = 1) : d138819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24280 q ha hb
    | true =>
      simp only [d1647, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24281 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d135431 q = 1) : d138820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d135431 q = 1) : d138821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d135431 q = 1) : d138822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d135431 q = 1) : d138829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24282 q ha hb
    | true =>
      simp only [d1657, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24283 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d135431 q = 1) : d138830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d135431 q = 1) : d138831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d135431 q = 1) : d138844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24285 q ha hb
    | true =>
      simp only [d1683, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24268 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d135431 q = 1) : d138845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5649 q = 1) (hb : d135431 q = 1) : d138858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5649, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24287 q ha hb
    | true =>
      simp only [d5649, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5650 q = 1) (hb : d135431 q = 1) : d138859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5650, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5650, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74726 q = 1) (hb : d135431 q = 1) : d138860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74726, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74727 q = 1) (hb : d135431 q = 1) : d138861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74727, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74728 q = 1) (hb : d135431 q = 1) : d138862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74728, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1805 q = 1) (hb : d135431 q = 1) : d138866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d138866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24289 q ha hb
    | true =>
      simp only [d1805, d138866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24290 q ha hb
  have h16 (q : Pattern) (ha : d1806 q = 1) (hb : d135431 q = 1) : d138867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d138867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d138867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1807 q = 1) (hb : d135431 q = 1) : d138868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d138868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1807, d138868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1808 q = 1) (hb : d135431 q = 1) : d138869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d138869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d138869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1811 q = 1) (hb : d135431 q = 1) : d138872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d138872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24291 q ha hb
    | true =>
      simp only [d1811, d138872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24292 q ha hb
  have h20 (q : Pattern) (ha : d1812 q = 1) (hb : d135431 q = 1) : d138873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d138873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d138873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1813 q = 1) (hb : d135431 q = 1) : d138874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d138874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1813, d138874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d1815 q = 1) (hb : d135431 q = 1) : d138876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24293 q ha hb
    | true =>
      simp only [d1815, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24271 q ha hb
  have h23 (q : Pattern) (ha : d4530 q = 1) (hb : d135431 q = 1) : d138877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4530, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5656 q = 1) (hb : d135431 q = 1) : d138879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5656, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24294 q ha hb
    | true =>
      simp only [d5656, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5657 q = 1) (hb : d135431 q = 1) : d138880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5657, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5657, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74730 q = 1) (hb : d135431 q = 1) : d138881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74730, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74731 q = 1) (hb : d135431 q = 1) : d138882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74731, d138882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74731, d138882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74732 q = 1) (hb : d135431 q = 1) : d138883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74732, d138883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74732, d138883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74733 q = 1) (hb : d135431 q = 1) : d138884 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74733, d138884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74733, d138884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24296 (p : Pattern) (ha : d74740 p = 1) (hb : d135431 p = 1) : d138904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1815 q = 1) (hb : d135431 q = 1) : d138876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24293 q ha hb
    | true =>
      simp only [d1815, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24271 q ha hb
  have h2 (q : Pattern) (ha : d4530 q = 1) (hb : d135431 q = 1) : d138877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4530, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5656 q = 1) (hb : d135431 q = 1) : d138879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5656, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24294 q ha hb
    | true =>
      simp only [d5656, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5657 q = 1) (hb : d135431 q = 1) : d138880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5657, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5657, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74730 q = 1) (hb : d135431 q = 1) : d138881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74730, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74738 q = 1) (hb : d135431 q = 1) : d138902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74738, d138902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74738, d138902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74739 q = 1) (hb : d135431 q = 1) : d138903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74739, d138903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74739, d138903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74740 q = 1) (hb : d135431 q = 1) : d138904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d138904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74740, d138904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24297 (p : Pattern) (ha : d1894 p = 1) (hb : d135431 p = 1) : d138924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1867 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1874 q = 1) (hb : d135431 q = 1) : d138912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d135431, d138912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1874, d135431, d138912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
  have h3 (q : Pattern) (ha : d1875 q = 1) (hb : d135431 q = 1) : d138913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d138913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d138913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1876 q = 1) (hb : d135431 q = 1) : d138914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d138914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d138914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1873 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1879 q = 1) (hb : d135431 q = 1) : d138915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1879, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
  have h7 (q : Pattern) (ha : d1880 q = 1) (hb : d135431 q = 1) : d138916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1881 q = 1) (hb : d135431 q = 1) : d138917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1882 q = 1) (hb : d135431 q = 1) : d138918 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d138918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1882, d138918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1889 q = 1) (hb : d135431 q = 1) : d138919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h12 (q : Pattern) (ha : d1890 q = 1) (hb : d135431 q = 1) : d138920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1891 q = 1) (hb : d135431 q = 1) : d138921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1892 q = 1) (hb : d135431 q = 1) : d138922 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1892, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1893 q = 1) (hb : d135431 q = 1) : d138923 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d138923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1893, d138923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1894 q = 1) (hb : d135431 q = 1) : d138924 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d138924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1894, d138924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro24298 (p : Pattern) (ha : d1899 p = 1) (hb : d135431 p = 1) : d138929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1879 q = 1) (hb : d135431 q = 1) : d138915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
  have h3 (q : Pattern) (ha : d1880 q = 1) (hb : d135431 q = 1) : d138916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1881 q = 1) (hb : d135431 q = 1) : d138917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1889 q = 1) (hb : d135431 q = 1) : d138919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h7 (q : Pattern) (ha : d1890 q = 1) (hb : d135431 q = 1) : d138920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1891 q = 1) (hb : d135431 q = 1) : d138921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1892 q = 1) (hb : d135431 q = 1) : d138922 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1892, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1897 q = 1) (hb : d135431 q = 1) : d138927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1897, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1898 q = 1) (hb : d135431 q = 1) : d138928 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d138928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1898, d138928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1899 q = 1) (hb : d135431 q = 1) : d138929 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d138929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1899, d138929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro24299 (p : Pattern) (ha : d1905 p = 1) (hb : d135431 p = 1) : d138935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d135431 q = 1) : d138925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d138925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24297 q ha hb
    | true =>
      simp only [d1895, d138925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d135431 q = 1) : d138926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d138926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d138926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1900 q = 1) (hb : d135431 q = 1) : d138930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24298 q ha hb
    | true =>
      simp only [d1900, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1901 q = 1) (hb : d135431 q = 1) : d138931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1902 q = 1) (hb : d135431 q = 1) : d138932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1902, d138932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1902, d138932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1903 q = 1) (hb : d135431 q = 1) : d138933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1903, d138933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1903, d138933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1904 q = 1) (hb : d135431 q = 1) : d138934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1904, d138934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1904, d138934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1905 q = 1) (hb : d135431 q = 1) : d138935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1905, d138935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1905, d138935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24300 (p : Pattern) (ha : d1913 p = 1) (hb : d135431 p = 1) : d138943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d135431 q = 1) : d138930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24298 q ha hb
    | true =>
      simp only [d1900, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d135431 q = 1) : d138931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d135431 q = 1) : d138938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24277 q ha hb
    | true =>
      simp only [d1908, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d135431 q = 1) : d138939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1910 q = 1) (hb : d135431 q = 1) : d138940 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d138940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, d138940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1911 q = 1) (hb : d135431 q = 1) : d138941 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d138941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1911, d138941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1912 q = 1) (hb : d135431 q = 1) : d138942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d138942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1912, d138942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1913 q = 1) (hb : d135431 q = 1) : d138943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d138943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1913, d138943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24301 (p : Pattern) (ha : d5686 p = 1) (hb : d135431 p = 1) : d138951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1879 q = 1) (hb : d135431 q = 1) : d138915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
  have h3 (q : Pattern) (ha : d1880 q = 1) (hb : d135431 q = 1) : d138916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1881 q = 1) (hb : d135431 q = 1) : d138917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1889 q = 1) (hb : d135431 q = 1) : d138919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1889, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h7 (q : Pattern) (ha : d1890 q = 1) (hb : d135431 q = 1) : d138920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1891 q = 1) (hb : d135431 q = 1) : d138921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1892 q = 1) (hb : d135431 q = 1) : d138922 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1892, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5679 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5680 q = 1) (hb : d94753 q = 1) : d5680 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5681 q = 1) (hb : d135431 q = 1) : d138946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5681, d135431, d138946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d5681, d135431, d138946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5682 q = 1) (hb : d135431 q = 1) : d138947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5682, d138947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5682, d138947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5683 q = 1) (hb : d135431 q = 1) : d138948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5683, d138948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5683, d138948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5684 q = 1) (hb : d135431 q = 1) : d138949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5684, d138949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5684, d138949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5685 q = 1) (hb : d135431 q = 1) : d138950 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5685, d138950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5685, d138950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5686 q = 1) (hb : d135431 q = 1) : d138951 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5686, d138951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5686, d138951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24302 (p : Pattern) (ha : d5692 p = 1) (hb : d135431 p = 1) : d138957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5687 q = 1) (hb : d135431 q = 1) : d138952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5687, d138952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24301 q ha hb
    | true =>
      simp only [d5687, d138952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5688 q = 1) (hb : d135431 q = 1) : d138953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5688, d138953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5688, d138953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5689 q = 1) (hb : d135431 q = 1) : d138954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5689, d138954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5689, d138954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5690 q = 1) (hb : d135431 q = 1) : d138955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5690, d138955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5690, d138955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5691 q = 1) (hb : d135431 q = 1) : d138956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5691, d138956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5691, d138956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5692 q = 1) (hb : d135431 q = 1) : d138957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5692, d138957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5692, d138957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24303 (p : Pattern) (ha : d74749 p = 1) (hb : d135431 p = 1) : d138963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1914 q = 1) (hb : d135431 q = 1) : d138944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d138944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24299 q ha hb
    | true =>
      simp only [d1914, d138944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24300 q ha hb
  have h2 (q : Pattern) (ha : d4545 q = 1) (hb : d135431 q = 1) : d138945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d138945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4545, d138945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5693 q = 1) (hb : d135431 q = 1) : d138958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5693, d138958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24302 q ha hb
    | true =>
      simp only [d5693, d138958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5694 q = 1) (hb : d135431 q = 1) : d138959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5694, d138959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5694, d138959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74746 q = 1) (hb : d135431 q = 1) : d138960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74746, d138960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74746, d138960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74747 q = 1) (hb : d135431 q = 1) : d138961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d138961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74747, d138961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74748 q = 1) (hb : d135431 q = 1) : d138962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d138962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74748, d138962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74749 q = 1) (hb : d135431 q = 1) : d138963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d138963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74749, d138963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24304 (p : Pattern) (ha : d74755 p = 1) (hb : d135431 p = 1) : d138980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d135431 q = 1) : d138802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d138802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d138802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24270 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d135431 q = 1) : d138803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d138803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d138803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d135431 q = 1) : d138812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24270 q ha hb
    | true =>
      simp only [d1640, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24273 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d135431 q = 1) : d138813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d135431 q = 1) : d138814 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d138814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d138814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74734 q = 1) (hb : d135431 q = 1) : d138885 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74734, d138885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24288 q ha hb
    | true =>
      simp only [d74734, d138885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24295 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d135431 q = 1) : d138898 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d138898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24274 q ha hb
    | true =>
      simp only [d1839, d138898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24275 q ha hb
  have h8 (q : Pattern) (ha : d74735 q = 1) (hb : d135431 q = 1) : d138899 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74735, d138899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74735, d138899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74736 q = 1) (hb : d135431 q = 1) : d138900 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d138900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74736, d138900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74737 q = 1) (hb : d135431 q = 1) : d138901 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d138901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74737, d138901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74741 q = 1) (hb : d135431 q = 1) : d138905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d138905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74741, d138905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24296 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d135431 q = 1) : d138907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d138907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d138907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24276 q ha hb
  have h13 (q : Pattern) (ha : d74742 q = 1) (hb : d135431 q = 1) : d138908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d138908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74742, d138908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74743 q = 1) (hb : d135431 q = 1) : d138909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d138909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74743, d138909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74744 q = 1) (hb : d135431 q = 1) : d138910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d138910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74744, d138910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74745 q = 1) (hb : d135431 q = 1) : d138911 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d138911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74745, d138911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74750 q = 1) (hb : d135431 q = 1) : d138964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d138964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74750, d138964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24303 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d135431 q = 1) : d138975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d138975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d138975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24279 q ha hb
  have h19 (q : Pattern) (ha : d74751 q = 1) (hb : d135431 q = 1) : d138976 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d138976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74751, d138976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74752 q = 1) (hb : d135431 q = 1) : d138977 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d138977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74752, d138977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74753 q = 1) (hb : d135431 q = 1) : d138978 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d138978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74753, d138978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74754 q = 1) (hb : d135431 q = 1) : d138979 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d138979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74754, d138979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74755 q = 1) (hb : d135431 q = 1) : d138980 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d138980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74755, d138980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24305 (p : Pattern) (ha : d74761 p = 1) (hb : d135431 p = 1) : d138986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74756 q = 1) (hb : d135431 q = 1) : d138981 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d138981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74756, d138981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24304 q ha hb
  have h2 (q : Pattern) (ha : d74757 q = 1) (hb : d135431 q = 1) : d138982 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d138982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74757, d138982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74758 q = 1) (hb : d135431 q = 1) : d138983 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d138983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74758, d138983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74759 q = 1) (hb : d135431 q = 1) : d138984 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d138984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74759, d138984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74760 q = 1) (hb : d135431 q = 1) : d138985 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d138985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74760, d138985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74761 q = 1) (hb : d135431 q = 1) : d138986 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d138986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74761, d138986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24306 (p : Pattern) (ha : d2092 p = 1) (hb : d135431 p = 1) : d139000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2073 q = 1) (hb : d135431 q = 1) : d138991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2073, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
  have h3 (q : Pattern) (ha : d2074 q = 1) (hb : d135431 q = 1) : d138992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2075 q = 1) (hb : d135431 q = 1) : d138993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2086 q = 1) (hb : d135431 q = 1) : d138994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h7 (q : Pattern) (ha : d2087 q = 1) (hb : d135431 q = 1) : d138995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2088 q = 1) (hb : d135431 q = 1) : d138996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2089 q = 1) (hb : d135431 q = 1) : d138997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2089, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2090 q = 1) (hb : d135431 q = 1) : d138998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2090, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2091 q = 1) (hb : d135431 q = 1) : d138999 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2091, d138999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2091, d138999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2092 q = 1) (hb : d135431 q = 1) : d139000 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2092, d139000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2092, d139000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro24307 (p : Pattern) (ha : d2096 p = 1) (hb : d135431 p = 1) : d139004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2086 q = 1) (hb : d135431 q = 1) : d138994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h3 (q : Pattern) (ha : d2087 q = 1) (hb : d135431 q = 1) : d138995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2088 q = 1) (hb : d135431 q = 1) : d138996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2090 q = 1) (hb : d135431 q = 1) : d138998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2090, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2095 q = 1) (hb : d135431 q = 1) : d139003 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d139003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2095, d139003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2096 q = 1) (hb : d135431 q = 1) : d139004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d139004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2096, d139004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24308 (p : Pattern) (ha : d2102 p = 1) (hb : d135431 p = 1) : d139010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d135431 q = 1) : d139007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d135431 q = 1) : d139008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d135431 q = 1) : d139009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2102 q = 1) (hb : d135431 q = 1) : d139010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d139010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d139010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24309 (p : Pattern) (ha : d2106 p = 1) (hb : d135431 p = 1) : d139014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d135431 q = 1) : d139013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d135431 q = 1) : d139014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d139014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d139014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24310 (p : Pattern) (ha : d2112 p = 1) (hb : d135431 p = 1) : d139020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d135431 q = 1) : d139015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24308 q ha hb
    | true =>
      simp only [d2107, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24309 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d135431 q = 1) : d139016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d135431 q = 1) : d139017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d135431 q = 1) : d139018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d135431 q = 1) : d139019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2112 q = 1) (hb : d135431 q = 1) : d139020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d139020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d139020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24311 (p : Pattern) (ha : d2115 p = 1) (hb : d135431 p = 1) : d139023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d135431 q = 1) : d139007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d135431 q = 1) : d139008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d135431 q = 1) : d139009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2115 q = 1) (hb : d135431 q = 1) : d139023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, d139023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2115, d139023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24312 (p : Pattern) (ha : d2116 p = 1) (hb : d135431 p = 1) : d139024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d135431 q = 1) : d139013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d135431 q = 1) : d139024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d139024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, d139024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24313 (p : Pattern) (ha : d2122 p = 1) (hb : d135431 p = 1) : d139030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d135431 q = 1) : d139015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24308 q ha hb
    | true =>
      simp only [d2107, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24309 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d135431 q = 1) : d139016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d135431 q = 1) : d139017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d135431 q = 1) : d139018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d135431 q = 1) : d139019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2117 q = 1) (hb : d135431 q = 1) : d139025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24311 q ha hb
    | true =>
      simp only [d2117, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24312 q ha hb
  have h7 (q : Pattern) (ha : d2118 q = 1) (hb : d135431 q = 1) : d139026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2119 q = 1) (hb : d135431 q = 1) : d139027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2119, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2120 q = 1) (hb : d135431 q = 1) : d139028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2121 q = 1) (hb : d135431 q = 1) : d139029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2122 q = 1) (hb : d135431 q = 1) : d139030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d139030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2122, d139030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24314 (p : Pattern) (ha : d2310 p = 1) (hb : d135431 p = 1) : d139110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d135431 q = 1) : d139015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24308 q ha hb
    | true =>
      simp only [d2107, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24309 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d135431 q = 1) : d139016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d135431 q = 1) : d139017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d135431 q = 1) : d139018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d135431 q = 1) : d139019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d135431 q = 1) : d139105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24309 q ha hb
    | true =>
      simp only [d2305, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d135431 q = 1) : d139106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d135431 q = 1) : d139107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d135431 q = 1) : d139108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d135431 q = 1) : d139109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2310 q = 1) (hb : d135431 q = 1) : d139110 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, d139110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2310, d139110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24315 (p : Pattern) (ha : d2316 p = 1) (hb : d135431 p = 1) : d139116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d135431 q = 1) : d139105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24309 q ha hb
    | true =>
      simp only [d2305, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d135431 q = 1) : d139106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d135431 q = 1) : d139107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d135431 q = 1) : d139108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d135431 q = 1) : d139109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d135431 q = 1) : d139111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24312 q ha hb
    | true =>
      simp only [d2311, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d135431 q = 1) : d139112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d135431 q = 1) : d139113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d135431 q = 1) : d139114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d135431 q = 1) : d139115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d135431 q = 1) : d139116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d139116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, d139116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24316 (p : Pattern) (ha : d2325 p = 1) (hb : d135431 p = 1) : d139125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d135431 q = 1) : d139111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24312 q ha hb
    | true =>
      simp only [d2311, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d135431 q = 1) : d139112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d135431 q = 1) : d139113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d135431 q = 1) : d139114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d135431 q = 1) : d139115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d135431 q = 1) : d139125 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d139125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d139125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24317 (p : Pattern) (ha : d2385 p = 1) (hb : d135431 p = 1) : d139156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2367 q = 1) (hb : d135431 q = 1) : d139138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h3 (q : Pattern) (ha : d2368 q = 1) (hb : d135431 q = 1) : d139139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2369 q = 1) (hb : d135431 q = 1) : d139140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2375 q = 1) (hb : d135431 q = 1) : d139146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2375, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2384 q = 1) (hb : d135431 q = 1) : d139155 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d139155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2384, d139155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2385 q = 1) (hb : d135431 q = 1) : d139156 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d139156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2385, d139156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24318 (p : Pattern) (ha : d2452 p = 1) (hb : d135431 p = 1) : d139187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d135431 q = 1) : d139157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24317 q ha hb
    | true =>
      simp only [d2386, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d135431 q = 1) : d139158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d135431 q = 1) : d139184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d139184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d139184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d135431 q = 1) : d139185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d139185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d139185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d135431 q = 1) : d139186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d139186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d139186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d135431 q = 1) : d139187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d139187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d139187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24319 (p : Pattern) (ha : d2458 p = 1) (hb : d135431 p = 1) : d139193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d135431 q = 1) : d139188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d139188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24318 q ha hb
    | true =>
      simp only [d2453, d139188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d135431 q = 1) : d139189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d139189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d139189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d135431 q = 1) : d139190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d139190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d139190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d135431 q = 1) : d139191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d139191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d139191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d135431 q = 1) : d139192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d139192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d139192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d135431 q = 1) : d139193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d139193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d139193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24320 (p : Pattern) (ha : d2127 p = 1) (hb : d135431 p = 1) : d139035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d135431 q = 1) : d139007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d135431 q = 1) : d139008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d135431 q = 1) : d139034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2127 q = 1) (hb : d135431 q = 1) : d139035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d139035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d139035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24321 (p : Pattern) (ha : d2129 p = 1) (hb : d135431 p = 1) : d139037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d135431 q = 1) : d139036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d135431 q = 1) : d139037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d139037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d139037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24322 (p : Pattern) (ha : d2136 p = 1) (hb : d135431 p = 1) : d139044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d135431 q = 1) : d139007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d135431 q = 1) : d139042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d135431 q = 1) : d139043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2136 q = 1) (hb : d135431 q = 1) : d139044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d139044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d139044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24323 (p : Pattern) (ha : d2139 p = 1) (hb : d135431 p = 1) : d139047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d135431 q = 1) : d139045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d135431 q = 1) : d139046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d135431 q = 1) : d139047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d139047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d139047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24324 (p : Pattern) (ha : d2155 p = 1) (hb : d135431 p = 1) : d139056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2149 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2150 q = 1) (hb : d135431 q = 1) : d139051 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d135431, d139051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2150, d135431, d139051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
  have h3 (q : Pattern) (ha : d2151 q = 1) (hb : d135431 q = 1) : d139052 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d139052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d139052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2152 q = 1) (hb : d135431 q = 1) : d139053 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d139053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d139053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2070 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2073 q = 1) (hb : d135431 q = 1) : d138991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2073, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
  have h7 (q : Pattern) (ha : d2074 q = 1) (hb : d135431 q = 1) : d138992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2075 q = 1) (hb : d135431 q = 1) : d138993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2153 q = 1) (hb : d135431 q = 1) : d139054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d139054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2153, d139054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2086 q = 1) (hb : d135431 q = 1) : d138994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h12 (q : Pattern) (ha : d2087 q = 1) (hb : d135431 q = 1) : d138995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2088 q = 1) (hb : d135431 q = 1) : d138996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2089 q = 1) (hb : d135431 q = 1) : d138997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2089, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2154 q = 1) (hb : d135431 q = 1) : d139055 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2154, d139055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2154, d139055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2155 q = 1) (hb : d135431 q = 1) : d139056 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2155, d139056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2155, d139056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro24325 (p : Pattern) (ha : d2161 p = 1) (hb : d135431 p = 1) : d139062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d135431 q = 1) : d139057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24324 q ha hb
    | true =>
      simp only [d2156, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d135431 q = 1) : d139058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2158 q = 1) (hb : d135431 q = 1) : d139059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2158, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d135431 q = 1) : d139060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2159, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d135431 q = 1) : d139061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2161 q = 1) (hb : d135431 q = 1) : d139062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2161, d139062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2161, d139062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24326 (p : Pattern) (ha : d5733 p = 1) (hb : d135431 p = 1) : d139070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2073 q = 1) (hb : d135431 q = 1) : d138991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2073, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
  have h3 (q : Pattern) (ha : d2074 q = 1) (hb : d135431 q = 1) : d138992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2075 q = 1) (hb : d135431 q = 1) : d138993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2086 q = 1) (hb : d135431 q = 1) : d138994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2086, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h7 (q : Pattern) (ha : d2087 q = 1) (hb : d135431 q = 1) : d138995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2088 q = 1) (hb : d135431 q = 1) : d138996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2089 q = 1) (hb : d135431 q = 1) : d138997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2089, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5726 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5727 q = 1) (hb : d94753 q = 1) : d5727 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5728 q = 1) (hb : d135431 q = 1) : d139065 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5728, d135431, d139065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d5728, d135431, d139065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5729 q = 1) (hb : d135431 q = 1) : d139066 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5729, d139066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5729, d139066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5730 q = 1) (hb : d135431 q = 1) : d139067 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5730, d139067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5730, d139067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5731 q = 1) (hb : d135431 q = 1) : d139068 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5731, d139068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5731, d139068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5732 q = 1) (hb : d135431 q = 1) : d139069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5732, d139069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5732, d139069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5733 q = 1) (hb : d135431 q = 1) : d139070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5733, d139070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5733, d139070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24327 (p : Pattern) (ha : d5739 p = 1) (hb : d135431 p = 1) : d139076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5734 q = 1) (hb : d135431 q = 1) : d139071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5734, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24326 q ha hb
    | true =>
      simp only [d5734, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5735 q = 1) (hb : d135431 q = 1) : d139072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5735, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5735, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5736 q = 1) (hb : d135431 q = 1) : d139073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5736, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5736, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5737 q = 1) (hb : d135431 q = 1) : d139074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5737, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5737, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5738 q = 1) (hb : d135431 q = 1) : d139075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5738, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5738, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5739 q = 1) (hb : d135431 q = 1) : d139076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5739, d139076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5739, d139076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24328 (p : Pattern) (ha : d74769 p = 1) (hb : d135431 p = 1) : d139082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d135431 q = 1) : d139038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24320 q ha hb
    | true =>
      simp only [d2130, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24321 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d135431 q = 1) : d139039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d135431 q = 1) : d139040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d135431 q = 1) : d139041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d135431 q = 1) : d139048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24322 q ha hb
    | true =>
      simp only [d2140, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24323 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d135431 q = 1) : d139049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d135431 q = 1) : d139050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d135431 q = 1) : d139063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24325 q ha hb
    | true =>
      simp only [d2162, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24308 q ha hb
  have h9 (q : Pattern) (ha : d4566 q = 1) (hb : d135431 q = 1) : d139064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5740 q = 1) (hb : d135431 q = 1) : d139077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5740, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24327 q ha hb
    | true =>
      simp only [d5740, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5741 q = 1) (hb : d135431 q = 1) : d139078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5741, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5741, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74766 q = 1) (hb : d135431 q = 1) : d139079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74766, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74766, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74767 q = 1) (hb : d135431 q = 1) : d139080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74767, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74768 q = 1) (hb : d135431 q = 1) : d139081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74768, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74769 q = 1) (hb : d135431 q = 1) : d139082 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74769, d139082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74769, d139082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24329 (p : Pattern) (ha : d2281 p = 1) (hb : d135431 p = 1) : d139083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d135431 q = 1) : d139007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d135431 q = 1) : d139008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d135431 q = 1) : d139034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2281 q = 1) (hb : d135431 q = 1) : d139083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, d139083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2281, d139083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24330 (p : Pattern) (ha : d2282 p = 1) (hb : d135431 p = 1) : d139084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d135431 q = 1) : d139036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d135431 q = 1) : d139084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d139084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, d139084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24331 (p : Pattern) (ha : d2287 p = 1) (hb : d135431 p = 1) : d139089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d135431 q = 1) : d139007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d135431 q = 1) : d139042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d135431 q = 1) : d139043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2287 q = 1) (hb : d135431 q = 1) : d139089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, d139089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2287, d139089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24332 (p : Pattern) (ha : d2288 p = 1) (hb : d135431 p = 1) : d139090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24307 q ha hb
    | true =>
      simp only [d2097, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d135431 q = 1) : d139045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d135431 q = 1) : d139046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d135431 q = 1) : d139090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d139090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, d139090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24333 (p : Pattern) (ha : d2292 p = 1) (hb : d135431 p = 1) : d139094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d135431 q = 1) : d139057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24324 q ha hb
    | true =>
      simp only [d2156, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d135431 q = 1) : d139058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2093 q = 1) (hb : d135431 q = 1) : d139001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24306 q ha hb
    | true =>
      simp only [d2093, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d135431 q = 1) : d139002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2158 q = 1) (hb : d135431 q = 1) : d139059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2158, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d135431 q = 1) : d139060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2159, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d135431 q = 1) : d139061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2292 q = 1) (hb : d135431 q = 1) : d139094 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2292, d139094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2292, d139094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24334 (p : Pattern) (ha : d5746 p = 1) (hb : d135431 p = 1) : d139097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5734 q = 1) (hb : d135431 q = 1) : d139071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5734, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24326 q ha hb
    | true =>
      simp only [d5734, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5735 q = 1) (hb : d135431 q = 1) : d139072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5735, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5735, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5736 q = 1) (hb : d135431 q = 1) : d139073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5736, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5736, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5737 q = 1) (hb : d135431 q = 1) : d139074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5737, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5737, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5738 q = 1) (hb : d135431 q = 1) : d139075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5738, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5738, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5746 q = 1) (hb : d135431 q = 1) : d139097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5746, d139097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5746, d139097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24335 (p : Pattern) (ha : d74773 p = 1) (hb : d135431 p = 1) : d139103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d135431 q = 1) : d139038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24320 q ha hb
    | true =>
      simp only [d2130, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24321 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d135431 q = 1) : d139039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d135431 q = 1) : d139040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d135431 q = 1) : d139041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d135431 q = 1) : d139048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24322 q ha hb
    | true =>
      simp only [d2140, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24323 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d135431 q = 1) : d139049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d135431 q = 1) : d139050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d135431 q = 1) : d139063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24325 q ha hb
    | true =>
      simp only [d2162, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24308 q ha hb
  have h9 (q : Pattern) (ha : d4566 q = 1) (hb : d135431 q = 1) : d139064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5740 q = 1) (hb : d135431 q = 1) : d139077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5740, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24327 q ha hb
    | true =>
      simp only [d5740, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5741 q = 1) (hb : d135431 q = 1) : d139078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5741, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5741, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74766 q = 1) (hb : d135431 q = 1) : d139079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74766, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74766, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74767 q = 1) (hb : d135431 q = 1) : d139080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74767, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74768 q = 1) (hb : d135431 q = 1) : d139081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74768, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2283 q = 1) (hb : d135431 q = 1) : d139085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d139085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24329 q ha hb
    | true =>
      simp only [d2283, d139085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24330 q ha hb
  have h16 (q : Pattern) (ha : d2284 q = 1) (hb : d135431 q = 1) : d139086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d139086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d139086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2285 q = 1) (hb : d135431 q = 1) : d139087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d139087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d2285, d139087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d2286 q = 1) (hb : d135431 q = 1) : d139088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d139088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d139088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2289 q = 1) (hb : d135431 q = 1) : d139091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d139091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24331 q ha hb
    | true =>
      simp only [d2289, d139091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24332 q ha hb
  have h20 (q : Pattern) (ha : d2290 q = 1) (hb : d135431 q = 1) : d139092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d139092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d139092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d2291 q = 1) (hb : d135431 q = 1) : d139093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d139093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d2291, d139093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d2293 q = 1) (hb : d135431 q = 1) : d139095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24333 q ha hb
    | true =>
      simp only [d2293, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24311 q ha hb
  have h23 (q : Pattern) (ha : d4571 q = 1) (hb : d135431 q = 1) : d139096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4571, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5747 q = 1) (hb : d135431 q = 1) : d139098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5747, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24334 q ha hb
    | true =>
      simp only [d5747, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5748 q = 1) (hb : d135431 q = 1) : d139099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5748, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5748, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74770 q = 1) (hb : d135431 q = 1) : d139100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74770, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74770, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74771 q = 1) (hb : d135431 q = 1) : d139101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74771, d139101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74771, d139101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74772 q = 1) (hb : d135431 q = 1) : d139102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74772, d139102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74772, d139102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74773 q = 1) (hb : d135431 q = 1) : d139103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74773, d139103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74773, d139103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24336 (p : Pattern) (ha : d74780 p = 1) (hb : d135431 p = 1) : d139123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2293 q = 1) (hb : d135431 q = 1) : d139095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24333 q ha hb
    | true =>
      simp only [d2293, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24311 q ha hb
  have h2 (q : Pattern) (ha : d4571 q = 1) (hb : d135431 q = 1) : d139096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4571, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5747 q = 1) (hb : d135431 q = 1) : d139098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5747, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24334 q ha hb
    | true =>
      simp only [d5747, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5748 q = 1) (hb : d135431 q = 1) : d139099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5748, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5748, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74770 q = 1) (hb : d135431 q = 1) : d139100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74770, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74770, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74778 q = 1) (hb : d135431 q = 1) : d139121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74778, d139121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74778, d139121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74779 q = 1) (hb : d135431 q = 1) : d139122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74779, d139122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74779, d139122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74780 q = 1) (hb : d135431 q = 1) : d139123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d139123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74780, d139123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24337 (p : Pattern) (ha : d2372 p = 1) (hb : d135431 p = 1) : d139143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2345 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2352 q = 1) (hb : d135431 q = 1) : d139131 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d135431, d139131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2352, d135431, d139131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
  have h3 (q : Pattern) (ha : d2353 q = 1) (hb : d135431 q = 1) : d139132 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d139132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d139132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2354 q = 1) (hb : d135431 q = 1) : d139133 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d139133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d139133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2351 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2357 q = 1) (hb : d135431 q = 1) : d139134 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2357, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
  have h7 (q : Pattern) (ha : d2358 q = 1) (hb : d135431 q = 1) : d139135 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2359 q = 1) (hb : d135431 q = 1) : d139136 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2360 q = 1) (hb : d135431 q = 1) : d139137 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d139137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2360, d139137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2367 q = 1) (hb : d135431 q = 1) : d139138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h12 (q : Pattern) (ha : d2368 q = 1) (hb : d135431 q = 1) : d139139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2369 q = 1) (hb : d135431 q = 1) : d139140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2370 q = 1) (hb : d135431 q = 1) : d139141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2370, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2371 q = 1) (hb : d135431 q = 1) : d139142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d139142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2371, d139142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2372 q = 1) (hb : d135431 q = 1) : d139143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d139143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2372, d139143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro24338 (p : Pattern) (ha : d2377 p = 1) (hb : d135431 p = 1) : d139148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2357 q = 1) (hb : d135431 q = 1) : d139134 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2357, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
  have h3 (q : Pattern) (ha : d2358 q = 1) (hb : d135431 q = 1) : d139135 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2359 q = 1) (hb : d135431 q = 1) : d139136 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2367 q = 1) (hb : d135431 q = 1) : d139138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h7 (q : Pattern) (ha : d2368 q = 1) (hb : d135431 q = 1) : d139139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2369 q = 1) (hb : d135431 q = 1) : d139140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2370 q = 1) (hb : d135431 q = 1) : d139141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2370, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2375 q = 1) (hb : d135431 q = 1) : d139146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2375, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2376 q = 1) (hb : d135431 q = 1) : d139147 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d139147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2376, d139147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2377 q = 1) (hb : d135431 q = 1) : d139148 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d139148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2377, d139148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro24339 (p : Pattern) (ha : d2383 p = 1) (hb : d135431 p = 1) : d139154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d135431 q = 1) : d139144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d139144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24337 q ha hb
    | true =>
      simp only [d2373, d139144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d135431 q = 1) : d139145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d139145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d139145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2378 q = 1) (hb : d135431 q = 1) : d139149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24338 q ha hb
    | true =>
      simp only [d2378, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2379 q = 1) (hb : d135431 q = 1) : d139150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2380 q = 1) (hb : d135431 q = 1) : d139151 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2380, d139151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2380, d139151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2381 q = 1) (hb : d135431 q = 1) : d139152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2381, d139152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2381, d139152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2382 q = 1) (hb : d135431 q = 1) : d139153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2382, d139153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2382, d139153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2383 q = 1) (hb : d135431 q = 1) : d139154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2383, d139154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2383, d139154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24340 (p : Pattern) (ha : d2391 p = 1) (hb : d135431 p = 1) : d139162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d135431 q = 1) : d139149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24338 q ha hb
    | true =>
      simp only [d2378, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d135431 q = 1) : d139150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d135431 q = 1) : d139157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24317 q ha hb
    | true =>
      simp only [d2386, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d135431 q = 1) : d139158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2388 q = 1) (hb : d135431 q = 1) : d139159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d139159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2388, d139159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2389 q = 1) (hb : d135431 q = 1) : d139160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d139160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2389, d139160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2390 q = 1) (hb : d135431 q = 1) : d139161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d139161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2390, d139161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2391 q = 1) (hb : d135431 q = 1) : d139162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d139162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2391, d139162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24341 (p : Pattern) (ha : d5777 p = 1) (hb : d135431 p = 1) : d139170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2357 q = 1) (hb : d135431 q = 1) : d139134 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2357, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
  have h3 (q : Pattern) (ha : d2358 q = 1) (hb : d135431 q = 1) : d139135 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2359 q = 1) (hb : d135431 q = 1) : d139136 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2367 q = 1) (hb : d135431 q = 1) : d139138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2367, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h7 (q : Pattern) (ha : d2368 q = 1) (hb : d135431 q = 1) : d139139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2369 q = 1) (hb : d135431 q = 1) : d139140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2370 q = 1) (hb : d135431 q = 1) : d139141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2370, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5770 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5771 q = 1) (hb : d94753 q = 1) : d5771 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5772 q = 1) (hb : d135431 q = 1) : d139165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5772, d135431, d139165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d5772, d135431, d139165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5773 q = 1) (hb : d135431 q = 1) : d139166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5773, d139166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5773, d139166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5774 q = 1) (hb : d135431 q = 1) : d139167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5774, d139167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5774, d139167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5775 q = 1) (hb : d135431 q = 1) : d139168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5775, d139168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5775, d139168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5776 q = 1) (hb : d135431 q = 1) : d139169 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5776, d139169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5776, d139169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5777 q = 1) (hb : d135431 q = 1) : d139170 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5777, d139170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5777, d139170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24342 (p : Pattern) (ha : d5783 p = 1) (hb : d135431 p = 1) : d139176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5778 q = 1) (hb : d135431 q = 1) : d139171 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5778, d139171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24341 q ha hb
    | true =>
      simp only [d5778, d139171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5779 q = 1) (hb : d135431 q = 1) : d139172 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5779, d139172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5779, d139172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5780 q = 1) (hb : d135431 q = 1) : d139173 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5780, d139173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5780, d139173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5781 q = 1) (hb : d135431 q = 1) : d139174 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5781, d139174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5781, d139174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5782 q = 1) (hb : d135431 q = 1) : d139175 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5782, d139175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5782, d139175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5783 q = 1) (hb : d135431 q = 1) : d139176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5783, d139176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5783, d139176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24343 (p : Pattern) (ha : d74789 p = 1) (hb : d135431 p = 1) : d139182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2392 q = 1) (hb : d135431 q = 1) : d139163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d139163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24339 q ha hb
    | true =>
      simp only [d2392, d139163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24340 q ha hb
  have h2 (q : Pattern) (ha : d4586 q = 1) (hb : d135431 q = 1) : d139164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d139164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4586, d139164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5784 q = 1) (hb : d135431 q = 1) : d139177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5784, d139177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24342 q ha hb
    | true =>
      simp only [d5784, d139177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5785 q = 1) (hb : d135431 q = 1) : d139178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5785, d139178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5785, d139178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74786 q = 1) (hb : d135431 q = 1) : d139179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74786, d139179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74786, d139179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74787 q = 1) (hb : d135431 q = 1) : d139180 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d139180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74787, d139180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74788 q = 1) (hb : d135431 q = 1) : d139181 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d139181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74788, d139181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74789 q = 1) (hb : d135431 q = 1) : d139182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d139182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74789, d139182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24344 (p : Pattern) (ha : d74795 p = 1) (hb : d135431 p = 1) : d139199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d135431 q = 1) : d139021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d139021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d139021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24310 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d135431 q = 1) : d139022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d139022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d139022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d135431 q = 1) : d139031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24310 q ha hb
    | true =>
      simp only [d2123, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24313 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d135431 q = 1) : d139032 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d135431 q = 1) : d139033 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d139033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d139033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74774 q = 1) (hb : d135431 q = 1) : d139104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74774, d139104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24328 q ha hb
    | true =>
      simp only [d74774, d139104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24335 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d135431 q = 1) : d139117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d139117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24314 q ha hb
    | true =>
      simp only [d2317, d139117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24315 q ha hb
  have h8 (q : Pattern) (ha : d74775 q = 1) (hb : d135431 q = 1) : d139118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74775, d139118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74775, d139118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74776 q = 1) (hb : d135431 q = 1) : d139119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d139119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74776, d139119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74777 q = 1) (hb : d135431 q = 1) : d139120 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d139120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74777, d139120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74781 q = 1) (hb : d135431 q = 1) : d139124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d139124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74781, d139124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24336 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d135431 q = 1) : d139126 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d139126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d139126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24316 q ha hb
  have h13 (q : Pattern) (ha : d74782 q = 1) (hb : d135431 q = 1) : d139127 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d139127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74782, d139127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74783 q = 1) (hb : d135431 q = 1) : d139128 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d139128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74783, d139128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74784 q = 1) (hb : d135431 q = 1) : d139129 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d139129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74784, d139129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74785 q = 1) (hb : d135431 q = 1) : d139130 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d139130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74785, d139130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74790 q = 1) (hb : d135431 q = 1) : d139183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d139183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74790, d139183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24343 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d135431 q = 1) : d139194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d139194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d139194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24319 q ha hb
  have h19 (q : Pattern) (ha : d74791 q = 1) (hb : d135431 q = 1) : d139195 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d139195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74791, d139195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74792 q = 1) (hb : d135431 q = 1) : d139196 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d139196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74792, d139196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74793 q = 1) (hb : d135431 q = 1) : d139197 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d139197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74793, d139197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74794 q = 1) (hb : d135431 q = 1) : d139198 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d139198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74794, d139198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74795 q = 1) (hb : d135431 q = 1) : d139199 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d139199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74795, d139199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24345 (p : Pattern) (ha : d74801 p = 1) (hb : d135431 p = 1) : d139205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74796 q = 1) (hb : d135431 q = 1) : d139200 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d139200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74796, d139200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24344 q ha hb
  have h2 (q : Pattern) (ha : d74797 q = 1) (hb : d135431 q = 1) : d139201 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d139201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74797, d139201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74798 q = 1) (hb : d135431 q = 1) : d139202 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d139202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74798, d139202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74799 q = 1) (hb : d135431 q = 1) : d139203 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d139203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74799, d139203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74800 q = 1) (hb : d135431 q = 1) : d139204 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d139204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74800, d139204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74801 q = 1) (hb : d135431 q = 1) : d139205 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d139205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74801, d139205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24346 (p : Pattern) (ha : d74807 p = 1) (hb : d135431 p = 1) : d139211 p = 1 := by
  have h0 (q : Pattern) (ha : d74648 q = 1) (hb : d135431 q = 1) : d138336 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d138336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24147 q ha hb
    | true =>
      simp only [d74648, d138336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24185 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74685 q = 1) (hb : d135431 q = 1) : d138552 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d138552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74685, d138552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24225 q ha hb
  have h3 (q : Pattern) (ha : d74686 q = 1) (hb : d135431 q = 1) : d138553 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d138553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d138553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74723 q = 1) (hb : d135431 q = 1) : d138769 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d138769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74723, d138769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24265 q ha hb
  have h5 (q : Pattern) (ha : d74724 q = 1) (hb : d135431 q = 1) : d138770 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d138770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74724, d138770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74725 q = 1) (hb : d135431 q = 1) : d138771 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d138771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d138771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74762 q = 1) (hb : d135431 q = 1) : d138987 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d138987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74762, d138987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24305 q ha hb
  have h8 (q : Pattern) (ha : d74763 q = 1) (hb : d135431 q = 1) : d138988 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d138988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74763, d138988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74764 q = 1) (hb : d135431 q = 1) : d138989 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d138989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74764, d138989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74765 q = 1) (hb : d135431 q = 1) : d138990 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d138990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d138990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74802 q = 1) (hb : d135431 q = 1) : d139206 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d139206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74802, d139206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24345 q ha hb
  have h12 (q : Pattern) (ha : d74803 q = 1) (hb : d135431 q = 1) : d139207 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d139207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74803, d139207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74804 q = 1) (hb : d135431 q = 1) : d139208 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d139208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74804, d139208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74805 q = 1) (hb : d135431 q = 1) : d139209 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d139209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74805, d139209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74806 q = 1) (hb : d135431 q = 1) : d139210 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d139210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d139210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74807 q = 1) (hb : d135431 q = 1) : d139211 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d139211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d139211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro24347 (p : Pattern) (ha : d74813 p = 1) (hb : d135431 p = 1) : d139217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74808 q = 1) (hb : d135431 q = 1) : d139212 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d139212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24346 q ha hb
    | true =>
      simp only [d74808, d139212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74809 q = 1) (hb : d135431 q = 1) : d139213 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d139213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d139213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74810 q = 1) (hb : d135431 q = 1) : d139214 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d139214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d139214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74811 q = 1) (hb : d135431 q = 1) : d139215 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d139215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d139215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74812 q = 1) (hb : d135431 q = 1) : d139216 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d139216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d139216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74813 q = 1) (hb : d135431 q = 1) : d139217 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d139217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d139217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24348 (p : Pattern) (ha : d74819 p = 1) (hb : d135431 p = 1) : d139223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74814 q = 1) (hb : d135431 q = 1) : d139218 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d139218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24347 q ha hb
    | true =>
      simp only [d74814, d139218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74815 q = 1) (hb : d135431 q = 1) : d139219 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d139219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d139219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74816 q = 1) (hb : d135431 q = 1) : d139220 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d139220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d139220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74817 q = 1) (hb : d135431 q = 1) : d139221 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d139221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d139221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74818 q = 1) (hb : d135431 q = 1) : d139222 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d139222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d139222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74819 q = 1) (hb : d135431 q = 1) : d139223 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d139223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d139223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24349 (p : Pattern) (ha : d74825 p = 1) (hb : d135431 p = 1) : d139229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74820 q = 1) (hb : d135431 q = 1) : d139224 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d139224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24348 q ha hb
    | true =>
      simp only [d74820, d139224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74821 q = 1) (hb : d135431 q = 1) : d139225 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d139225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d139225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74822 q = 1) (hb : d135431 q = 1) : d139226 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d139226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d139226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74823 q = 1) (hb : d135431 q = 1) : d139227 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d139227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d139227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74824 q = 1) (hb : d135431 q = 1) : d139228 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d139228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d139228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74825 q = 1) (hb : d135431 q = 1) : d139229 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d139229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d139229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24350 (p : Pattern) (ha : d74831 p = 1) (hb : d135432 p = 1) : d139235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d135431 q = 1) : d139230 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d139230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24349 q ha hb
    | true =>
      simp only [d74826, d139230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d135431 q = 1) : d139231 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d139231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d139231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74828 q = 1) (hb : d135432 q = 1) : d139232 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d135432, d139232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d135432, d139232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74829 q = 1) (hb : d135432 q = 1) : d139233 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d139233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74829, d139233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74830 q = 1) (hb : d135432 q = 1) : d139234 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d139234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74830, d139234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d74831 q = 1) (hb : d135432 q = 1) : d139235 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d139235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74831, d139235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro24351 (p : Pattern) (ha : d74837 p = 1) (hb : d135432 p = 1) : d139241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d135432 q = 1) : d139236 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d139236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24350 q ha hb
    | true =>
      simp only [d74832, d139236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d135432 q = 1) : d139237 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d139237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d139237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d135432 q = 1) : d139238 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d139238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d139238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d135432 q = 1) : d139239 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d139239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d139239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d135432 q = 1) : d139240 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d139240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d139240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d135432 q = 1) : d139241 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d139241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d139241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24352 (p : Pattern) (ha : d74843 p = 1) (hb : d135432 p = 1) : d139247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d135432 q = 1) : d139242 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d139242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24351 q ha hb
    | true =>
      simp only [d74838, d139242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d135432 q = 1) : d139243 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d139243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d139243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d135432 q = 1) : d139244 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d139244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d139244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d135432 q = 1) : d139245 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d139245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d139245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d135432 q = 1) : d139246 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d139246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d139246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d135432 q = 1) : d139247 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d139247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d139247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24353 (p : Pattern) (ha : d74849 p = 1) (hb : d135432 p = 1) : d139253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d135432 q = 1) : d139248 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d139248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24352 q ha hb
    | true =>
      simp only [d74844, d139248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d135432 q = 1) : d139249 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d139249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d139249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d135432 q = 1) : d139250 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d139250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d139250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d135432 q = 1) : d139251 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d139251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d139251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d135432 q = 1) : d139252 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d139252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d139252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d135432 q = 1) : d139253 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d139253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d139253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24354 (p : Pattern) (ha : d136862 p = 1) (hb : d138044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51881 q = 1) (hb : d138039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q hb ha
  have h3 (q : Pattern) (ha : d136858 q = 1) (hb : d138040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136858, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136858, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136859 q = 1) (hb : d138041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136859, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136859, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136860 q = 1) (hb : d138042 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136860, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136860, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136861 q = 1) (hb : d138043 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136861, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136861, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136862 q = 1) (hb : d138044 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136862, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136862, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24355 (p : Pattern) (ha : d136868 p = 1) (hb : d138050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136865 q = 1) (hb : d138047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136866 q = 1) (hb : d138048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136867 q = 1) (hb : d138049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136867, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136867, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136868 q = 1) (hb : d138050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136868, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136868, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24356 (p : Pattern) (ha : d136874 p = 1) (hb : d138056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136870 q = 1) (hb : d138052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136871 q = 1) (hb : d138053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136871, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136871, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136872 q = 1) (hb : d138054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136872, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136872, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136873 q = 1) (hb : d138055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136873, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136873, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136874 q = 1) (hb : d138056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136874, d138056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136874, d138056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24357 (p : Pattern) (ha : d136875 p = 1) (hb : d138057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136865 q = 1) (hb : d138047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136866 q = 1) (hb : d138048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136867 q = 1) (hb : d138049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136867, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136867, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136875 q = 1) (hb : d138057 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136875, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136875, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24358 (p : Pattern) (ha : d136881 p = 1) (hb : d138063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136870 q = 1) (hb : d138052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136871 q = 1) (hb : d138053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136871, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136871, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136872 q = 1) (hb : d138054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136872, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136872, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136873 q = 1) (hb : d138055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136873, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136873, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136877 q = 1) (hb : d138059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136878 q = 1) (hb : d138060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136878, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136878, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d136879 q = 1) (hb : d138061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136879, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136879, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136880 q = 1) (hb : d138062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136880, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136880, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d136881 q = 1) (hb : d138063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136881, d138063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136881, d138063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24359 (p : Pattern) (ha : d136886 p = 1) (hb : d138068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136877 q = 1) (hb : d138059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136878 q = 1) (hb : d138060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136878, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136878, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136879 q = 1) (hb : d138061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136879, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136879, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136880 q = 1) (hb : d138062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136880, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136880, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136886 q = 1) (hb : d138068 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136886, d138068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136886, d138068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24360 (p : Pattern) (ha : d136896 p = 1) (hb : d138079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51922 q = 1) (hb : d138074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q hb ha
  have h3 (q : Pattern) (ha : d136892 q = 1) (hb : d138075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136892, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136892, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136893 q = 1) (hb : d138076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136893, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136893, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136894 q = 1) (hb : d138077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136894, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136894, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136895 q = 1) (hb : d138078 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136895, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136895, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136896 q = 1) (hb : d138079 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136896, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136896, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24361 (p : Pattern) (ha : d136902 p = 1) (hb : d138085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136897 q = 1) (hb : d138080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136897, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24360 q ha hb
    | true =>
      simp only [d136897, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136898 q = 1) (hb : d138081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136898, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136898, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136899 q = 1) (hb : d138082 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136899, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136899, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136900 q = 1) (hb : d138083 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136900, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136900, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136901 q = 1) (hb : d138084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136901, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136901, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136902 q = 1) (hb : d138085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136902, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136902, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24362 (p : Pattern) (ha : d136908 p = 1) (hb : d138091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136903 q = 1) (hb : d138086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24361 q ha hb
    | true =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136904 q = 1) (hb : d138087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136904, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136904, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136905 q = 1) (hb : d138088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136905, d138088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136905, d138088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136906 q = 1) (hb : d138089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136906, d138089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136906, d138089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136907 q = 1) (hb : d138090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136907, d138090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136907, d138090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136908 q = 1) (hb : d138091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136908, d138091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136908, d138091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24363 (p : Pattern) (ha : d136914 p = 1) (hb : d138097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136882 q = 1) (hb : d138064 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136882, d138064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24356 q ha hb
    | true =>
      simp only [d136882, d138064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24358 q ha hb
  have h2 (q : Pattern) (ha : d136883 q = 1) (hb : d138065 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136883, d138065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136883, d138065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136884 q = 1) (hb : d138066 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136884, d138066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136884, d138066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136885 q = 1) (hb : d138067 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136885, d138067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136885, d138067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136887 q = 1) (hb : d138069 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136887, d138069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136887, d138069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24359 q ha hb
  have h6 (q : Pattern) (ha : d136888 q = 1) (hb : d138070 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136888, d138070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136888, d138070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136889 q = 1) (hb : d138071 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136889, d138071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136889, d138071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136890 q = 1) (hb : d138072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136890, d138072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136890, d138072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d136891 q = 1) (hb : d138073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136891, d138073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136891, d138073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136909 q = 1) (hb : d138092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136909, d138092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136909, d138092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24362 q ha hb
  have h11 (q : Pattern) (ha : d136910 q = 1) (hb : d138093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136910, d138093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136910, d138093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d136911 q = 1) (hb : d138094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136911, d138094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136911, d138094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d136912 q = 1) (hb : d138095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136912, d138095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d136912, d138095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d136913 q = 1) (hb : d138096 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136913, d138096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d136913, d138096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d136914 q = 1) (hb : d138097 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136914, d138097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136914, d138097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24364 (p : Pattern) (ha : d136924 p = 1) (hb : d138107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136920 q = 1) (hb : d138103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136921 q = 1) (hb : d138104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136922 q = 1) (hb : d138105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136923 q = 1) (hb : d138106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136924 q = 1) (hb : d138107 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136924, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136924, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24365 (p : Pattern) (ha : d136931 p = 1) (hb : d138114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136920 q = 1) (hb : d138103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136921 q = 1) (hb : d138104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136922 q = 1) (hb : d138105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136923 q = 1) (hb : d138106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136927 q = 1) (hb : d138110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136927, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136927, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136928 q = 1) (hb : d138111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136928, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136928, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d136929 q = 1) (hb : d138112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136929, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136929, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136930 q = 1) (hb : d138113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136930, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136930, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d136931 q = 1) (hb : d138114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136931, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136931, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24366 (p : Pattern) (ha : d136936 p = 1) (hb : d138119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136865 q = 1) (hb : d138047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136866 q = 1) (hb : d138048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136935 q = 1) (hb : d138118 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136935, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136935, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136936 q = 1) (hb : d138119 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136936, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136936, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24367 (p : Pattern) (ha : d136943 p = 1) (hb : d138126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136865 q = 1) (hb : d138047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136941 q = 1) (hb : d138124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136941, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136941, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136942 q = 1) (hb : d138125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136942, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136942, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136943 q = 1) (hb : d138126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136943, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136943, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24368 (p : Pattern) (ha : d136951 p = 1) (hb : d138135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51994 q = 1) (hb : d138130 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q hb ha
  have h3 (q : Pattern) (ha : d136947 q = 1) (hb : d138131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136947, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136947, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136948 q = 1) (hb : d138132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136948, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136948, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51881 q = 1) (hb : d138039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q hb ha
  have h7 (q : Pattern) (ha : d136858 q = 1) (hb : d138040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136858, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136858, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136859 q = 1) (hb : d138041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136859, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136859, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136949 q = 1) (hb : d138133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136949, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136949, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136860 q = 1) (hb : d138042 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136860, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136860, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d136950 q = 1) (hb : d138134 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136950, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136950, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d136951 q = 1) (hb : d138135 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136951, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136951, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24369 (p : Pattern) (ha : d136957 p = 1) (hb : d138141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d138138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d138139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136956 q = 1) (hb : d138140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136956, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136956, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136957 q = 1) (hb : d138141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136957, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136957, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24370 (p : Pattern) (ha : d136963 p = 1) (hb : d138147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136937 q = 1) (hb : d138120 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136937, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24366 q ha hb
    | true =>
      simp only [d136937, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136938 q = 1) (hb : d138121 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136938, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136938, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136939 q = 1) (hb : d138122 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136939, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136939, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136940 q = 1) (hb : d138123 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136940, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136940, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136944 q = 1) (hb : d138127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136944, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24367 q ha hb
    | true =>
      simp only [d136944, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136945 q = 1) (hb : d138128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136945, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136945, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d136946 q = 1) (hb : d138129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136946, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136946, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d136959 q = 1) (hb : d138143 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136959, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136959, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d136870 q = 1) (hb : d138052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d136960 q = 1) (hb : d138144 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136960, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136960, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d136961 q = 1) (hb : d138145 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136961, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136961, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d136962 q = 1) (hb : d138146 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136962, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136962, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d136963 q = 1) (hb : d138147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136963, d138147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136963, d138147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24371 (p : Pattern) (ha : d136964 p = 1) (hb : d138148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136865 q = 1) (hb : d138047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136866 q = 1) (hb : d138048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136866, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136935 q = 1) (hb : d138118 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136935, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136935, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136964 q = 1) (hb : d138148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136964, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136964, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24372 (p : Pattern) (ha : d136969 p = 1) (hb : d138153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136865 q = 1) (hb : d138047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136865, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136941 q = 1) (hb : d138124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136941, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136941, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136942 q = 1) (hb : d138125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136942, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136942, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136969 q = 1) (hb : d138153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136969, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136969, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24373 (p : Pattern) (ha : d136973 p = 1) (hb : d138157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d138138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d138139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136956 q = 1) (hb : d138140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136956, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136956, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136973 q = 1) (hb : d138157 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136973, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136973, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24374 (p : Pattern) (ha : d136979 p = 1) (hb : d138163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136937 q = 1) (hb : d138120 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136937, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24366 q ha hb
    | true =>
      simp only [d136937, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136938 q = 1) (hb : d138121 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136938, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136938, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136939 q = 1) (hb : d138122 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136939, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136939, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136940 q = 1) (hb : d138123 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136940, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136940, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136944 q = 1) (hb : d138127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136944, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24367 q ha hb
    | true =>
      simp only [d136944, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136945 q = 1) (hb : d138128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136945, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136945, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d136946 q = 1) (hb : d138129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136946, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136946, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d136959 q = 1) (hb : d138143 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136959, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136959, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d136870 q = 1) (hb : d138052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136870, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d136960 q = 1) (hb : d138144 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136960, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136960, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d136961 q = 1) (hb : d138145 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136961, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136961, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d136962 q = 1) (hb : d138146 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136962, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136962, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d136965 q = 1) (hb : d138149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136965, d138149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24371 q ha hb
    | true =>
      simp only [d136965, d138149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d136966 q = 1) (hb : d138150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136966, d138150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136966, d138150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d136967 q = 1) (hb : d138151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136967, d138151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d136967, d138151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d136968 q = 1) (hb : d138152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136968, d138152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136968, d138152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d136970 q = 1) (hb : d138154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136970, d138154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24372 q ha hb
    | true =>
      simp only [d136970, d138154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d136971 q = 1) (hb : d138155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136971, d138155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136971, d138155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d136972 q = 1) (hb : d138156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136972, d138156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d136972, d138156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d136974 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
    | true =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d136975 q = 1) (hb : d138159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136975, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d136975, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d136877 q = 1) (hb : d138059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d136976 q = 1) (hb : d138160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136976, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d136976, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d136977 q = 1) (hb : d138161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136977, d138161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d136977, d138161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d136978 q = 1) (hb : d138162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136978, d138162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d136978, d138162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d136979 q = 1) (hb : d138163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136979, d138163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d136979, d138163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24375 (p : Pattern) (ha : d136981 p = 1) (hb : d138165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136920 q = 1) (hb : d138103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136921 q = 1) (hb : d138104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136922 q = 1) (hb : d138105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136923 q = 1) (hb : d138106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136981 q = 1) (hb : d138165 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136981, d138165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136981, d138165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24376 (p : Pattern) (ha : d136988 p = 1) (hb : d138172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136974 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
    | true =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d136975 q = 1) (hb : d138159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136975, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136975, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136877 q = 1) (hb : d138059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136877, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d136976 q = 1) (hb : d138160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136976, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136976, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d136986 q = 1) (hb : d138170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136986, d138170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136986, d138170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136987 q = 1) (hb : d138171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136987, d138171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136987, d138171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136988 q = 1) (hb : d138172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136988, d138172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136988, d138172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24377 (p : Pattern) (ha : d136998 p = 1) (hb : d138183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52048 q = 1) (hb : d138178 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q hb ha
  have h3 (q : Pattern) (ha : d136994 q = 1) (hb : d138179 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136994, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136994, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136995 q = 1) (hb : d138180 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136995, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136995, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51922 q = 1) (hb : d138074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q hb ha
  have h7 (q : Pattern) (ha : d136892 q = 1) (hb : d138075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136892, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136892, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136893 q = 1) (hb : d138076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136893, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136893, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136996 q = 1) (hb : d138181 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136996, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136996, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136894 q = 1) (hb : d138077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136894, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136894, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d136997 q = 1) (hb : d138182 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136997, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136997, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d136998 q = 1) (hb : d138183 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136998, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136998, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24378 (p : Pattern) (ha : d137004 p = 1) (hb : d138189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136999 q = 1) (hb : d138184 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136999, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24377 q ha hb
    | true =>
      simp only [d136999, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137000 q = 1) (hb : d138185 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137000, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137000, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136897 q = 1) (hb : d138080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136897, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24360 q ha hb
    | true =>
      simp only [d136897, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136898 q = 1) (hb : d138081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136898, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136898, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137001 q = 1) (hb : d138186 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137001, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137001, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137002 q = 1) (hb : d138187 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137002, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137002, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137003 q = 1) (hb : d138188 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137003, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137003, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137004 q = 1) (hb : d138189 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137004, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137004, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24379 (p : Pattern) (ha : d137010 p = 1) (hb : d138195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137005 q = 1) (hb : d138190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137005, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24378 q ha hb
    | true =>
      simp only [d137005, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24361 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136903 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137006 q = 1) (hb : d138191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137006, d138191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137006, d138191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d136903 q = 1) (hb : d138086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24361 q ha hb
    | true =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136904 q = 1) (hb : d138087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136904, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136904, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137007 q = 1) (hb : d138192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137007, d138192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137007, d138192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137008 q = 1) (hb : d138193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137008, d138193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137008, d138193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137009 q = 1) (hb : d138194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137009, d138194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137009, d138194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137010 q = 1) (hb : d138195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137010, d138195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137010, d138195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24380 (p : Pattern) (ha : d137016 p = 1) (hb : d138201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136925 q = 1) (hb : d138108 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136925, d138108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136925, d138108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24364 q ha hb
  have h2 (q : Pattern) (ha : d136926 q = 1) (hb : d138109 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136926, d138109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136926, d138109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136932 q = 1) (hb : d138115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136932, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24364 q ha hb
    | true =>
      simp only [d136932, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24365 q ha hb
  have h4 (q : Pattern) (ha : d136933 q = 1) (hb : d138116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136933, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136933, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136934 q = 1) (hb : d138117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136934, d138117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136934, d138117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136980 q = 1) (hb : d138164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136980, d138164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24370 q ha hb
    | true =>
      simp only [d136980, d138164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24374 q ha hb
  have h7 (q : Pattern) (ha : d136982 q = 1) (hb : d138166 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136982, d138166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24375 q ha hb
    | true =>
      simp only [d136982, d138166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136983 q = 1) (hb : d138167 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136983, d138167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136983, d138167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136984 q = 1) (hb : d138168 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136984, d138168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136984, d138168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d136985 q = 1) (hb : d138169 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136985, d138169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136985, d138169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d136989 q = 1) (hb : d138173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136989, d138173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136989, d138173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24376 q ha hb
  have h12 (q : Pattern) (ha : d136990 q = 1) (hb : d138174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136990, d138174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136990, d138174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d136991 q = 1) (hb : d138175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136991, d138175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d136991, d138175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d136992 q = 1) (hb : d138176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136992, d138176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d136992, d138176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d136993 q = 1) (hb : d138177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136993, d138177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136993, d138177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137011 q = 1) (hb : d138196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137011, d138196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137011, d138196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24379 q ha hb
  have h17 (q : Pattern) (ha : d137012 q = 1) (hb : d138197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137012, d138197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137012, d138197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d137013 q = 1) (hb : d138198 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137013, d138198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137013, d138198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137014 q = 1) (hb : d138199 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137014, d138199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d137014, d138199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d137015 q = 1) (hb : d138200 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137015, d138200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137015, d138200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137016 q = 1) (hb : d138201 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137016, d138201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137016, d138201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro24381 (p : Pattern) (ha : d137022 p = 1) (hb : d138207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136915 q = 1) (hb : d138098 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136915, d138098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136915, d138098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24363 q ha hb
  have h2 (q : Pattern) (ha : d136916 q = 1) (hb : d138099 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136916, d138099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136916, d138099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136917 q = 1) (hb : d138100 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136917, d138100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136917, d138100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136918 q = 1) (hb : d138101 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136918, d138101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136918, d138101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136919 q = 1) (hb : d138102 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136919, d138102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136919, d138102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137017 q = 1) (hb : d138202 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137017, d138202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137017, d138202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24380 q ha hb
  have h7 (q : Pattern) (ha : d137018 q = 1) (hb : d138203 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137018, d138203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137018, d138203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137019 q = 1) (hb : d138204 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137019, d138204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137019, d138204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137020 q = 1) (hb : d138205 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137020, d138205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137020, d138205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137021 q = 1) (hb : d138206 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137021, d138206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137021, d138206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137022 q = 1) (hb : d138207 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137022, d138207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137022, d138207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24382 (p : Pattern) (ha : d137027 p = 1) (hb : d138212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h2 (q : Pattern) (ha : d137023 q = 1) (hb : d138208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137023, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137023, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137024 q = 1) (hb : d138209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137024, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137024, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137025 q = 1) (hb : d138210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137025, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137025, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137026 q = 1) (hb : d138211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137026, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137026, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137027 q = 1) (hb : d138212 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137027, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137027, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24383 (p : Pattern) (ha : d137034 p = 1) (hb : d138219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h2 (q : Pattern) (ha : d137023 q = 1) (hb : d138208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137023, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137023, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137024 q = 1) (hb : d138209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137024, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137024, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137025 q = 1) (hb : d138210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137025, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137025, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137026 q = 1) (hb : d138211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137026, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137026, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136974 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
    | true =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
  have h7 (q : Pattern) (ha : d137030 q = 1) (hb : d138215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137030, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137030, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137031 q = 1) (hb : d138216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137031, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137031, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137032 q = 1) (hb : d138217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137032, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137032, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137033 q = 1) (hb : d138218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137033, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137033, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137034 q = 1) (hb : d138219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137034, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137034, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24384 (p : Pattern) (ha : d137039 p = 1) (hb : d138224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d138138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d138139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137038 q = 1) (hb : d138223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137038, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137038, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137039 q = 1) (hb : d138224 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137039, d138224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137039, d138224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24385 (p : Pattern) (ha : d137046 p = 1) (hb : d138231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d138138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137044 q = 1) (hb : d138229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137044, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137044, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137045 q = 1) (hb : d138230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137045, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137045, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137046 q = 1) (hb : d138231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137046, d138231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137046, d138231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24386 (p : Pattern) (ha : d137054 p = 1) (hb : d138240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52122 q = 1) (hb : d138235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12733 q hb ha
  have h3 (q : Pattern) (ha : d137050 q = 1) (hb : d138236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137050, d138236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137050, d138236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137051 q = 1) (hb : d138237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137051, d138237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137051, d138237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51994 q = 1) (hb : d138130 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q hb ha
  have h7 (q : Pattern) (ha : d136947 q = 1) (hb : d138131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136947, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136947, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136948 q = 1) (hb : d138132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136948, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136948, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137052 q = 1) (hb : d138238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137052, d138238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137052, d138238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51881 q = 1) (hb : d138039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q hb ha
  have h12 (q : Pattern) (ha : d136858 q = 1) (hb : d138040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136858, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136858, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d136859 q = 1) (hb : d138041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136859, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136859, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d136949 q = 1) (hb : d138133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136949, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136949, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137053 q = 1) (hb : d138239 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137053, d138239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137053, d138239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137054 q = 1) (hb : d138240 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137054, d138240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137054, d138240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24387 (p : Pattern) (ha : d137060 p = 1) (hb : d138246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137055 q = 1) (hb : d138241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137055, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24386 q ha hb
    | true =>
      simp only [d137055, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137056 q = 1) (hb : d138242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137056, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137056, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137057 q = 1) (hb : d138243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137057, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137057, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137058 q = 1) (hb : d138244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137058, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137058, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137059 q = 1) (hb : d138245 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137059, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137059, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137060 q = 1) (hb : d138246 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137060, d138246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137060, d138246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24388 (p : Pattern) (ha : d137066 p = 1) (hb : d138252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137063 q = 1) (hb : d138249 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137063, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137063, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137064 q = 1) (hb : d138250 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137064, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137064, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137065 q = 1) (hb : d138251 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137065, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137065, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137066 q = 1) (hb : d138252 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137066, d138252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137066, d138252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24389 (p : Pattern) (ha : d137072 p = 1) (hb : d138258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137040 q = 1) (hb : d138225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137040, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24384 q ha hb
    | true =>
      simp only [d137040, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24366 q ha hb
  have h2 (q : Pattern) (ha : d137041 q = 1) (hb : d138226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137041, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137041, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137042 q = 1) (hb : d138227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137042, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137042, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137043 q = 1) (hb : d138228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137043, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137043, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137047 q = 1) (hb : d138232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137047, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24385 q ha hb
    | true =>
      simp only [d137047, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24367 q ha hb
  have h6 (q : Pattern) (ha : d137048 q = 1) (hb : d138233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137048, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137048, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137049 q = 1) (hb : d138234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137049, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137049, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137061 q = 1) (hb : d138247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137061, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24387 q ha hb
    | true =>
      simp only [d137061, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137062 q = 1) (hb : d138248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137062, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137062, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137067 q = 1) (hb : d138253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137067, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24388 q ha hb
    | true =>
      simp only [d137067, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137068 q = 1) (hb : d138254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137068, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137068, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137069 q = 1) (hb : d138255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137069, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137069, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137070 q = 1) (hb : d138256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137070, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137070, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137071 q = 1) (hb : d138257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137071, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137071, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137072 q = 1) (hb : d138258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137072, d138258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137072, d138258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24390 (p : Pattern) (ha : d137073 p = 1) (hb : d138259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d138138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d138139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137038 q = 1) (hb : d138223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137038, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137038, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137073 q = 1) (hb : d138259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137073, d138259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137073, d138259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24391 (p : Pattern) (ha : d137078 p = 1) (hb : d138264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136863 q = 1) (hb : d138045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24354 q ha hb
    | true =>
      simp only [d136863, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136864 q = 1) (hb : d138046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136864, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d138138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137044 q = 1) (hb : d138229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137044, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137044, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137045 q = 1) (hb : d138230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137045, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137045, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137078 q = 1) (hb : d138264 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137078, d138264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137078, d138264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24392 (p : Pattern) (ha : d137082 p = 1) (hb : d138268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137055 q = 1) (hb : d138241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137055, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24386 q ha hb
    | true =>
      simp only [d137055, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137056 q = 1) (hb : d138242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137056, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137056, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137057 q = 1) (hb : d138243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137057, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137057, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137058 q = 1) (hb : d138244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137058, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137058, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137059 q = 1) (hb : d138245 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137059, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137059, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137082 q = 1) (hb : d138268 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137082, d138268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137082, d138268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24393 (p : Pattern) (ha : d137085 p = 1) (hb : d138271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d138136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24368 q ha hb
    | true =>
      simp only [d136952, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d138137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137063 q = 1) (hb : d138249 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137063, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137063, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137064 q = 1) (hb : d138250 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137064, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137064, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137065 q = 1) (hb : d138251 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137065, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137065, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137085 q = 1) (hb : d138271 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137085, d138271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137085, d138271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24394 (p : Pattern) (ha : d137091 p = 1) (hb : d138277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137040 q = 1) (hb : d138225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137040, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24384 q ha hb
    | true =>
      simp only [d137040, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24366 q ha hb
  have h2 (q : Pattern) (ha : d137041 q = 1) (hb : d138226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137041, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137041, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137042 q = 1) (hb : d138227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137042, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137042, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137043 q = 1) (hb : d138228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137043, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137043, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137047 q = 1) (hb : d138232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137047, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24385 q ha hb
    | true =>
      simp only [d137047, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24367 q ha hb
  have h6 (q : Pattern) (ha : d137048 q = 1) (hb : d138233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137048, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137048, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137049 q = 1) (hb : d138234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137049, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137049, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137061 q = 1) (hb : d138247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137061, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24387 q ha hb
    | true =>
      simp only [d137061, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137062 q = 1) (hb : d138248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137062, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137062, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137067 q = 1) (hb : d138253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137067, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24388 q ha hb
    | true =>
      simp only [d137067, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137068 q = 1) (hb : d138254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137068, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137068, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137069 q = 1) (hb : d138255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137069, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137069, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137070 q = 1) (hb : d138256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137070, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137070, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137071 q = 1) (hb : d138257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137071, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137071, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137074 q = 1) (hb : d138260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137074, d138260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24390 q ha hb
    | true =>
      simp only [d137074, d138260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24371 q ha hb
  have h17 (q : Pattern) (ha : d137075 q = 1) (hb : d138261 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137075, d138261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137075, d138261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137076 q = 1) (hb : d138262 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137076, d138262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137076, d138262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137077 q = 1) (hb : d138263 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137077, d138263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137077, d138263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137079 q = 1) (hb : d138265 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137079, d138265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24391 q ha hb
    | true =>
      simp only [d137079, d138265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24372 q ha hb
  have h21 (q : Pattern) (ha : d137080 q = 1) (hb : d138266 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137080, d138266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137080, d138266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137081 q = 1) (hb : d138267 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137081, d138267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137081, d138267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137083 q = 1) (hb : d138269 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137083, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24392 q ha hb
    | true =>
      simp only [d137083, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d137084 q = 1) (hb : d138270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137084, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d137084, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d137086 q = 1) (hb : d138272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137086, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24393 q ha hb
    | true =>
      simp only [d137086, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d137087 q = 1) (hb : d138273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137087, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d137087, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d137088 q = 1) (hb : d138274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137088, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d137088, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d137089 q = 1) (hb : d138275 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137089, d138275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d137089, d138275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d137090 q = 1) (hb : d138276 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137090, d138276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137090, d138276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d137091 q = 1) (hb : d138277 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137091, d138277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137091, d138277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24395 (p : Pattern) (ha : d137093 p = 1) (hb : d138279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h2 (q : Pattern) (ha : d137023 q = 1) (hb : d138208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137023, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137023, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137024 q = 1) (hb : d138209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137024, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137024, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137025 q = 1) (hb : d138210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137025, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137025, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137026 q = 1) (hb : d138211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137026, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137026, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136920 q = 1) (hb : d138103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136920, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136921 q = 1) (hb : d138104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136921, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d136922 q = 1) (hb : d138105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136922, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136923 q = 1) (hb : d138106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136923, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137093 q = 1) (hb : d138279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137093, d138279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137093, d138279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24396 (p : Pattern) (ha : d137100 p = 1) (hb : d138286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137083 q = 1) (hb : d138269 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137083, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24392 q ha hb
    | true =>
      simp only [d137083, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137084 q = 1) (hb : d138270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137084, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137084, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137086 q = 1) (hb : d138272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137086, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24393 q ha hb
    | true =>
      simp only [d137086, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137087 q = 1) (hb : d138273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137087, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137087, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137088 q = 1) (hb : d138274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137088, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137088, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137098 q = 1) (hb : d138284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137098, d138284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137098, d138284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137099 q = 1) (hb : d138285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137099, d138285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137099, d138285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137100 q = 1) (hb : d138286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137100, d138286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137100, d138286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24397 (p : Pattern) (ha : d137102 p = 1) (hb : d138288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136927 q = 1) (hb : d138110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136927, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136927, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136928 q = 1) (hb : d138111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136928, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136928, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136929 q = 1) (hb : d138112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136929, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136929, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136930 q = 1) (hb : d138113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136930, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136930, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137102 q = 1) (hb : d138288 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137102, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137102, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24398 (p : Pattern) (ha : d137112 p = 1) (hb : d138299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52182 q = 1) (hb : d138294 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12748 q hb ha
  have h3 (q : Pattern) (ha : d137108 q = 1) (hb : d138295 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137108, d138295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137108, d138295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137109 q = 1) (hb : d138296 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137109, d138296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137109, d138296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52048 q = 1) (hb : d138178 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q hb ha
  have h7 (q : Pattern) (ha : d136994 q = 1) (hb : d138179 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136994, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136994, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136995 q = 1) (hb : d138180 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136995, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136995, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137110 q = 1) (hb : d138297 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137110, d138297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137110, d138297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51922 q = 1) (hb : d138074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q hb ha
  have h12 (q : Pattern) (ha : d136892 q = 1) (hb : d138075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136892, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136892, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d136893 q = 1) (hb : d138076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136893, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136893, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d136996 q = 1) (hb : d138181 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136996, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136996, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137111 q = 1) (hb : d138298 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137111, d138298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137111, d138298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137112 q = 1) (hb : d138299 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137112, d138299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137112, d138299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24399 (p : Pattern) (ha : d137118 p = 1) (hb : d138305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137113 q = 1) (hb : d138300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137113, d138300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24398 q ha hb
    | true =>
      simp only [d137113, d138300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137114 q = 1) (hb : d138301 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137114, d138301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137114, d138301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136999 q = 1) (hb : d138184 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136999, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24377 q ha hb
    | true =>
      simp only [d136999, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137000 q = 1) (hb : d138185 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137000, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137000, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137115 q = 1) (hb : d138302 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137115, d138302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137115, d138302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137116 q = 1) (hb : d138303 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137116, d138303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137116, d138303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137117 q = 1) (hb : d138304 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137117, d138304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137117, d138304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137118 q = 1) (hb : d138305 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137118, d138305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137118, d138305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24400 (p : Pattern) (ha : d137124 p = 1) (hb : d138311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136999 q = 1) (hb : d138184 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136999, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24377 q ha hb
    | true =>
      simp only [d136999, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137000 q = 1) (hb : d138185 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137000, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137000, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137121 q = 1) (hb : d138308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137121, d138308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137121, d138308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137122 q = 1) (hb : d138309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137122, d138309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137122, d138309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137123 q = 1) (hb : d138310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137123, d138310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137123, d138310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137124 q = 1) (hb : d138311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137124, d138311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137124, d138311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24401 (p : Pattern) (ha : d137130 p = 1) (hb : d138317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137119 q = 1) (hb : d138306 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137119, d138306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24399 q ha hb
    | true =>
      simp only [d137119, d138306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24378 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137120 q = 1) (hb : d138307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137120, d138307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137120, d138307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137125 q = 1) (hb : d138312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137125, d138312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24400 q ha hb
    | true =>
      simp only [d137125, d138312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137126 q = 1) (hb : d138313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137126, d138313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137126, d138313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137127 q = 1) (hb : d138314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137127, d138314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137127, d138314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137128 q = 1) (hb : d138315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137128, d138315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137128, d138315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137129 q = 1) (hb : d138316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137129, d138316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137129, d138316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137130 q = 1) (hb : d138317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137130, d138317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137130, d138317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24402 (p : Pattern) (ha : d137136 p = 1) (hb : d138323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136903 q = 1) (hb : d138086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24361 q ha hb
    | true =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137132 q = 1) (hb : d138319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137132, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137132, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137133 q = 1) (hb : d138320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137133, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137133, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137134 q = 1) (hb : d138321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137134, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137134, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137135 q = 1) (hb : d138322 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137135, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137135, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137136 q = 1) (hb : d138323 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137136, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137136, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24403 (p : Pattern) (ha : d137142 p = 1) (hb : d138329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137028 q = 1) (hb : d138213 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137028, d138213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137028, d138213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24382 q ha hb
  have h2 (q : Pattern) (ha : d137029 q = 1) (hb : d138214 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137029, d138214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137029, d138214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137035 q = 1) (hb : d138220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137035, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24382 q ha hb
    | true =>
      simp only [d137035, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24383 q ha hb
  have h4 (q : Pattern) (ha : d137036 q = 1) (hb : d138221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137036, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137036, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137037 q = 1) (hb : d138222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137037, d138222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137037, d138222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137092 q = 1) (hb : d138278 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137092, d138278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24389 q ha hb
    | true =>
      simp only [d137092, d138278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24394 q ha hb
  have h7 (q : Pattern) (ha : d137094 q = 1) (hb : d138280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137094, d138280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24395 q ha hb
    | true =>
      simp only [d137094, d138280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24365 q ha hb
  have h8 (q : Pattern) (ha : d137095 q = 1) (hb : d138281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137095, d138281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137095, d138281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137096 q = 1) (hb : d138282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137096, d138282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137096, d138282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d137097 q = 1) (hb : d138283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137097, d138283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137097, d138283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137101 q = 1) (hb : d138287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137101, d138287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137101, d138287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24396 q ha hb
  have h12 (q : Pattern) (ha : d137103 q = 1) (hb : d138289 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137103, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137103, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24397 q ha hb
  have h13 (q : Pattern) (ha : d137104 q = 1) (hb : d138290 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137104, d138290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137104, d138290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137105 q = 1) (hb : d138291 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137105, d138291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137105, d138291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137106 q = 1) (hb : d138292 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137106, d138292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d137106, d138292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d137107 q = 1) (hb : d138293 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137107, d138293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137107, d138293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137131 q = 1) (hb : d138318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137131, d138318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137131, d138318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24401 q ha hb
  have h18 (q : Pattern) (ha : d137137 q = 1) (hb : d138324 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137137, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137137, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24402 q ha hb
  have h19 (q : Pattern) (ha : d137138 q = 1) (hb : d138325 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137138, d138325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137138, d138325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137139 q = 1) (hb : d138326 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137139, d138326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137139, d138326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137140 q = 1) (hb : d138327 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137140, d138327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d137140, d138327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d137141 q = 1) (hb : d138328 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137141, d138328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137141, d138328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137142 q = 1) (hb : d138329 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137142, d138329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137142, d138329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24404 (p : Pattern) (ha : d137148 p = 1) (hb : d138335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137143 q = 1) (hb : d138330 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137143, d138330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137143, d138330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24403 q ha hb
  have h2 (q : Pattern) (ha : d137144 q = 1) (hb : d138331 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137144, d138331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137144, d138331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137145 q = 1) (hb : d138332 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137145, d138332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137145, d138332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137146 q = 1) (hb : d138333 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137146, d138333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137146, d138333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137147 q = 1) (hb : d138334 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137147, d138334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137147, d138334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137148 q = 1) (hb : d138335 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137148, d138335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137148, d138335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24405 (p : Pattern) (ha : d137157 p = 1) (hb : d138346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52432 q = 1) (hb : d138337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q hb ha
  have h3 (q : Pattern) (ha : d137150 q = 1) (hb : d138338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137150, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137150, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137151 q = 1) (hb : d138339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137151, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137151, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52434 q = 1) (hb : d138340 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q hb ha
  have h7 (q : Pattern) (ha : d137152 q = 1) (hb : d138341 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137153 q = 1) (hb : d138342 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137154 q = 1) (hb : d138343 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137154, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137154, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137155 q = 1) (hb : d138344 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137155, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137155, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137156 q = 1) (hb : d138345 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137156, d138345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137156, d138345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137157 q = 1) (hb : d138346 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137157, d138346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137157, d138346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24406 (p : Pattern) (ha : d137161 p = 1) (hb : d138350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52434 q = 1) (hb : d138340 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q hb ha
  have h3 (q : Pattern) (ha : d137152 q = 1) (hb : d138341 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137153 q = 1) (hb : d138342 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137155 q = 1) (hb : d138344 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137155, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137155, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137160 q = 1) (hb : d138349 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137160, d138349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137160, d138349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137161 q = 1) (hb : d138350 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137161, d138350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137161, d138350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24407 (p : Pattern) (ha : d137167 p = 1) (hb : d138356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d138353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d138354 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137166 q = 1) (hb : d138355 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137166, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137166, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137167 q = 1) (hb : d138356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137167, d138356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137167, d138356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24408 (p : Pattern) (ha : d137171 p = 1) (hb : d138360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137168 q = 1) (hb : d138357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137169 q = 1) (hb : d138358 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137170 q = 1) (hb : d138359 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137170, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137170, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137171 q = 1) (hb : d138360 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137171, d138360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137171, d138360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24409 (p : Pattern) (ha : d137177 p = 1) (hb : d138366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137172 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
    | true =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
  have h2 (q : Pattern) (ha : d137173 q = 1) (hb : d138362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137173, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137173, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137174 q = 1) (hb : d138363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137174, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137174, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137175 q = 1) (hb : d138364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137175, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137175, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137176 q = 1) (hb : d138365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137176, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137176, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137177 q = 1) (hb : d138366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137177, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137177, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24410 (p : Pattern) (ha : d137180 p = 1) (hb : d138369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d138353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d138354 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137166 q = 1) (hb : d138355 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137166, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137166, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137180 q = 1) (hb : d138369 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137180, d138369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137180, d138369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24411 (p : Pattern) (ha : d137181 p = 1) (hb : d138370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137168 q = 1) (hb : d138357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137169 q = 1) (hb : d138358 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137170 q = 1) (hb : d138359 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137170, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137170, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137181 q = 1) (hb : d138370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137181, d138370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137181, d138370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24412 (p : Pattern) (ha : d137187 p = 1) (hb : d138376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137172 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
    | true =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
  have h2 (q : Pattern) (ha : d137173 q = 1) (hb : d138362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137173, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137173, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137174 q = 1) (hb : d138363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137174, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137174, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137175 q = 1) (hb : d138364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137175, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137175, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137176 q = 1) (hb : d138365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137176, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137176, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137182 q = 1) (hb : d138371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137182, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24410 q ha hb
    | true =>
      simp only [d137182, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24411 q ha hb
  have h7 (q : Pattern) (ha : d137183 q = 1) (hb : d138372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137183, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137183, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137184 q = 1) (hb : d138373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137184, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137184, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137185 q = 1) (hb : d138374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137185, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137185, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137186 q = 1) (hb : d138375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137186, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137186, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137187 q = 1) (hb : d138376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137187, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137187, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24413 (p : Pattern) (ha : d137192 p = 1) (hb : d138381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d138353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d138354 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137191 q = 1) (hb : d138380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137191, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137191, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137192 q = 1) (hb : d138381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137192, d138381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137192, d138381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24414 (p : Pattern) (ha : d137194 p = 1) (hb : d138383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137168 q = 1) (hb : d138357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137169 q = 1) (hb : d138358 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137193 q = 1) (hb : d138382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137193, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137193, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137194 q = 1) (hb : d138383 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137194, d138383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137194, d138383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24415 (p : Pattern) (ha : d137201 p = 1) (hb : d138390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d138353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137199 q = 1) (hb : d138388 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137199, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137199, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137200 q = 1) (hb : d138389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137200, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137200, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137201 q = 1) (hb : d138390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137201, d138390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137201, d138390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24416 (p : Pattern) (ha : d137204 p = 1) (hb : d138393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137168 q = 1) (hb : d138357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137202 q = 1) (hb : d138391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137202, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137202, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137203 q = 1) (hb : d138392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137203, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137203, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137204 q = 1) (hb : d138393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137204, d138393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137204, d138393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24417 (p : Pattern) (ha : d137212 p = 1) (hb : d138402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52294 q = 1) (hb : d138397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12767 q hb ha
  have h3 (q : Pattern) (ha : d137208 q = 1) (hb : d138398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137208, d138398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137208, d138398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137209 q = 1) (hb : d138399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137209, d138399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137209, d138399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52432 q = 1) (hb : d138337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q hb ha
  have h7 (q : Pattern) (ha : d137150 q = 1) (hb : d138338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137150, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137150, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137151 q = 1) (hb : d138339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137151, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137151, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137210 q = 1) (hb : d138400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137210, d138400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137210, d138400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52434 q = 1) (hb : d138340 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q hb ha
  have h12 (q : Pattern) (ha : d137152 q = 1) (hb : d138341 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137153 q = 1) (hb : d138342 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137154 q = 1) (hb : d138343 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137154, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137154, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137211 q = 1) (hb : d138401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137211, d138401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137211, d138401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137212 q = 1) (hb : d138402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137212, d138402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137212, d138402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24418 (p : Pattern) (ha : d137218 p = 1) (hb : d138408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137213 q = 1) (hb : d138403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137213, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24417 q ha hb
    | true =>
      simp only [d137213, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137214 q = 1) (hb : d138404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137214, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137214, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137215 q = 1) (hb : d138405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137215, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137215, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137216 q = 1) (hb : d138406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137216, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137216, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137217 q = 1) (hb : d138407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137217, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137217, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137218 q = 1) (hb : d138408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137218, d138408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137218, d138408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24419 (p : Pattern) (ha : d5457 p = 1) (hb : d74181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d74177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d74178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d74179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d74180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5455 q = 1) (hb : d74181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d74181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d74181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74181 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5457 q = 1) (hb : d74181 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24420 (p : Pattern) (ha : d137225 p = 1) (hb : d138416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52432 q = 1) (hb : d138337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q hb ha
  have h3 (q : Pattern) (ha : d137150 q = 1) (hb : d138338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137150, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137150, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137151 q = 1) (hb : d138339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137151, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137151, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52434 q = 1) (hb : d138340 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q hb ha
  have h7 (q : Pattern) (ha : d137152 q = 1) (hb : d138341 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137152, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137153 q = 1) (hb : d138342 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137153, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137154 q = 1) (hb : d138343 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137154, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137154, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74181 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74181 q = 1) (hb : d138411 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24419 q hb ha
  have h12 (q : Pattern) (ha : d137221 q = 1) (hb : d138412 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137221, d138412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137221, d138412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137222 q = 1) (hb : d138413 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137222, d138413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137222, d138413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137223 q = 1) (hb : d138414 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137223, d138414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137223, d138414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137224 q = 1) (hb : d138415 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137224, d138415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137224, d138415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137225 q = 1) (hb : d138416 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137225, d138416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137225, d138416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24421 (p : Pattern) (ha : d137231 p = 1) (hb : d138422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137226 q = 1) (hb : d138417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137226, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24420 q ha hb
    | true =>
      simp only [d137226, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137227 q = 1) (hb : d138418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137227, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137227, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137228 q = 1) (hb : d138419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137228, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137228, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137229 q = 1) (hb : d138420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137229, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137229, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137230 q = 1) (hb : d138421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137230, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137230, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137231 q = 1) (hb : d138422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137231, d138422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137231, d138422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24422 (p : Pattern) (ha : d137237 p = 1) (hb : d138428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137195 q = 1) (hb : d138384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137195, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24413 q ha hb
    | true =>
      simp only [d137195, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24414 q ha hb
  have h2 (q : Pattern) (ha : d137196 q = 1) (hb : d138385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137196, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137196, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137197 q = 1) (hb : d138386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137197, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137197, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137198 q = 1) (hb : d138387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137198, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137198, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137205 q = 1) (hb : d138394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137205, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24415 q ha hb
    | true =>
      simp only [d137205, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24416 q ha hb
  have h6 (q : Pattern) (ha : d137206 q = 1) (hb : d138395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137206, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137206, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137207 q = 1) (hb : d138396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137207, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137207, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137219 q = 1) (hb : d138409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137219, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24418 q ha hb
    | true =>
      simp only [d137219, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137172 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137220 q = 1) (hb : d138410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137220, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137220, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137232 q = 1) (hb : d138423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137232, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24421 q ha hb
    | true =>
      simp only [d137232, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137233 q = 1) (hb : d138424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137233, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137233, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137234 q = 1) (hb : d138425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137234, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137234, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137235 q = 1) (hb : d138426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137235, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137235, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137236 q = 1) (hb : d138427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137236, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137236, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137237 q = 1) (hb : d138428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137237, d138428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137237, d138428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24423 (p : Pattern) (ha : d137238 p = 1) (hb : d138429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d138353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d138354 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137191 q = 1) (hb : d138380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137191, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137191, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137238 q = 1) (hb : d138429 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137238, d138429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137238, d138429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24424 (p : Pattern) (ha : d137239 p = 1) (hb : d138430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137168 q = 1) (hb : d138357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137169 q = 1) (hb : d138358 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137169, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137193 q = 1) (hb : d138382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137193, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137193, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137239 q = 1) (hb : d138430 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137239, d138430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137239, d138430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24425 (p : Pattern) (ha : d137244 p = 1) (hb : d138435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d138353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137199 q = 1) (hb : d138388 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137199, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137199, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137200 q = 1) (hb : d138389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137200, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137200, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137244 q = 1) (hb : d138435 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137244, d138435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137244, d138435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24426 (p : Pattern) (ha : d137245 p = 1) (hb : d138436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137162 q = 1) (hb : d138351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24406 q ha hb
    | true =>
      simp only [d137162, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137163 q = 1) (hb : d138352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137163, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137168 q = 1) (hb : d138357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137168, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137202 q = 1) (hb : d138391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137202, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137202, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137203 q = 1) (hb : d138392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137203, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137203, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137245 q = 1) (hb : d138436 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137245, d138436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137245, d138436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24427 (p : Pattern) (ha : d137249 p = 1) (hb : d138440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137213 q = 1) (hb : d138403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137213, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24417 q ha hb
    | true =>
      simp only [d137213, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137214 q = 1) (hb : d138404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137214, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137214, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137158 q = 1) (hb : d138347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24405 q ha hb
    | true =>
      simp only [d137158, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137159 q = 1) (hb : d138348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137215 q = 1) (hb : d138405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137215, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137215, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137216 q = 1) (hb : d138406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137216, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137216, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137217 q = 1) (hb : d138407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137217, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137217, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137249 q = 1) (hb : d138440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137249, d138440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137249, d138440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24428 (p : Pattern) (ha : d137252 p = 1) (hb : d138443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137226 q = 1) (hb : d138417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137226, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24420 q ha hb
    | true =>
      simp only [d137226, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137227 q = 1) (hb : d138418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137227, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137227, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137228 q = 1) (hb : d138419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137228, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137228, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137229 q = 1) (hb : d138420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137229, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137229, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137230 q = 1) (hb : d138421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137230, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137230, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137252 q = 1) (hb : d138443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137252, d138443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137252, d138443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24429 (p : Pattern) (ha : d137258 p = 1) (hb : d138449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137195 q = 1) (hb : d138384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137195, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24413 q ha hb
    | true =>
      simp only [d137195, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24414 q ha hb
  have h2 (q : Pattern) (ha : d137196 q = 1) (hb : d138385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137196, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137196, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137197 q = 1) (hb : d138386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137197, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137197, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137198 q = 1) (hb : d138387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137198, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137198, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137205 q = 1) (hb : d138394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137205, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24415 q ha hb
    | true =>
      simp only [d137205, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24416 q ha hb
  have h6 (q : Pattern) (ha : d137206 q = 1) (hb : d138395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137206, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137206, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137207 q = 1) (hb : d138396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137207, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137207, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137219 q = 1) (hb : d138409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137219, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24418 q ha hb
    | true =>
      simp only [d137219, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137172 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137220 q = 1) (hb : d138410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137220, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137220, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137232 q = 1) (hb : d138423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137232, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24421 q ha hb
    | true =>
      simp only [d137232, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137233 q = 1) (hb : d138424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137233, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137233, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137234 q = 1) (hb : d138425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137234, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137234, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137235 q = 1) (hb : d138426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137235, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137235, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137236 q = 1) (hb : d138427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137236, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137236, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137240 q = 1) (hb : d138431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137240, d138431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24423 q ha hb
    | true =>
      simp only [d137240, d138431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24424 q ha hb
  have h17 (q : Pattern) (ha : d137241 q = 1) (hb : d138432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137241, d138432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137241, d138432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137242 q = 1) (hb : d138433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137242, d138433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137242, d138433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137243 q = 1) (hb : d138434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137243, d138434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137243, d138434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137246 q = 1) (hb : d138437 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137246, d138437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24425 q ha hb
    | true =>
      simp only [d137246, d138437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24426 q ha hb
  have h21 (q : Pattern) (ha : d137247 q = 1) (hb : d138438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137247, d138438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137247, d138438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137248 q = 1) (hb : d138439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137248, d138439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137248, d138439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137250 q = 1) (hb : d138441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137250, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24427 q ha hb
    | true =>
      simp only [d137250, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24410 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d137182 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d137251 q = 1) (hb : d138442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137251, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d137251, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d137253 q = 1) (hb : d138444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137253, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24428 q ha hb
    | true =>
      simp only [d137253, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d137254 q = 1) (hb : d138445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137254, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d137254, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d137255 q = 1) (hb : d138446 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137255, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d137255, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d137256 q = 1) (hb : d138447 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137256, d138447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d137256, d138447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d137257 q = 1) (hb : d138448 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137257, d138448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137257, d138448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d137258 q = 1) (hb : d138449 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137258, d138449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137258, d138449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24430 (p : Pattern) (ha : d137265 p = 1) (hb : d138456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137172 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
    | true =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
  have h2 (q : Pattern) (ha : d137173 q = 1) (hb : d138362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137173, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137173, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137174 q = 1) (hb : d138363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137174, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137174, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137175 q = 1) (hb : d138364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137175, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137175, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137176 q = 1) (hb : d138365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137176, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137176, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137260 q = 1) (hb : d138451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137260, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
    | true =>
      simp only [d137260, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137261 q = 1) (hb : d138452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137261, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137261, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137262 q = 1) (hb : d138453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137262, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137262, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137263 q = 1) (hb : d138454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137263, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137263, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137264 q = 1) (hb : d138455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137264, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137264, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137265 q = 1) (hb : d138456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137265, d138456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137265, d138456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24431 (p : Pattern) (ha : d137271 p = 1) (hb : d138462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137260 q = 1) (hb : d138451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137260, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
    | true =>
      simp only [d137260, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137261 q = 1) (hb : d138452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137261, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137261, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137262 q = 1) (hb : d138453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137262, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137262, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137263 q = 1) (hb : d138454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137263, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137263, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137264 q = 1) (hb : d138455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137264, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137264, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137266 q = 1) (hb : d138457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137266, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24411 q ha hb
    | true =>
      simp only [d137266, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137267 q = 1) (hb : d138458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137267, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137267, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137268 q = 1) (hb : d138459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137268, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137268, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137269 q = 1) (hb : d138460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137269, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137269, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137270 q = 1) (hb : d138461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137270, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137270, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137271 q = 1) (hb : d138462 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137271, d138462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137271, d138462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24432 (p : Pattern) (ha : d137278 p = 1) (hb : d138469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137250 q = 1) (hb : d138441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137250, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24427 q ha hb
    | true =>
      simp only [d137250, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24410 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137182 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137251 q = 1) (hb : d138442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137251, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137251, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137253 q = 1) (hb : d138444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137253, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24428 q ha hb
    | true =>
      simp only [d137253, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137254 q = 1) (hb : d138445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137254, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137254, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137255 q = 1) (hb : d138446 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137255, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137255, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137276 q = 1) (hb : d138467 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137276, d138467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137276, d138467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137277 q = 1) (hb : d138468 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137277, d138468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137277, d138468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137278 q = 1) (hb : d138469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137278, d138469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137278, d138469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24433 (p : Pattern) (ha : d137280 p = 1) (hb : d138471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137266 q = 1) (hb : d138457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137266, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24411 q ha hb
    | true =>
      simp only [d137266, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137267 q = 1) (hb : d138458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137267, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137267, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137268 q = 1) (hb : d138459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137268, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137268, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137269 q = 1) (hb : d138460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137269, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137269, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137270 q = 1) (hb : d138461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137270, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137270, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137280 q = 1) (hb : d138471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137280, d138471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137280, d138471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24434 (p : Pattern) (ha : d137295 p = 1) (hb : d138489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52367 q = 1) (hb : d138477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12784 q hb ha
  have h3 (q : Pattern) (ha : d137286 q = 1) (hb : d138478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137286, d138478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137286, d138478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137287 q = 1) (hb : d138479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137287, d138479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137287, d138479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52594 q = 1) (hb : d138480 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q hb ha
  have h7 (q : Pattern) (ha : d137288 q = 1) (hb : d138481 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137288, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137288, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137289 q = 1) (hb : d138482 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137289, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137289, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137290 q = 1) (hb : d138483 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137290, d138483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137290, d138483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52599 q = 1) (hb : d138484 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q hb ha
  have h12 (q : Pattern) (ha : d137291 q = 1) (hb : d138485 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137292 q = 1) (hb : d138486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137293 q = 1) (hb : d138487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137293, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137293, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137294 q = 1) (hb : d138488 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137294, d138488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137294, d138488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137295 q = 1) (hb : d138489 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137295, d138489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137295, d138489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24435 (p : Pattern) (ha : d137300 p = 1) (hb : d138494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52594 q = 1) (hb : d138480 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q hb ha
  have h3 (q : Pattern) (ha : d137288 q = 1) (hb : d138481 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137288, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137288, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137289 q = 1) (hb : d138482 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137289, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137289, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52599 q = 1) (hb : d138484 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q hb ha
  have h7 (q : Pattern) (ha : d137291 q = 1) (hb : d138485 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137292 q = 1) (hb : d138486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137293 q = 1) (hb : d138487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137293, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137293, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137298 q = 1) (hb : d138492 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137298, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137298, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137299 q = 1) (hb : d138493 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137299, d138493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137299, d138493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137300 q = 1) (hb : d138494 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137300, d138494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137300, d138494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24436 (p : Pattern) (ha : d137306 p = 1) (hb : d138500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137296 q = 1) (hb : d138490 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137296, d138490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24434 q ha hb
    | true =>
      simp only [d137296, d138490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137297 q = 1) (hb : d138491 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137297, d138491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137297, d138491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137301 q = 1) (hb : d138495 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137301, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24435 q ha hb
    | true =>
      simp only [d137301, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137302 q = 1) (hb : d138496 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137302, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137302, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137303 q = 1) (hb : d138497 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137303, d138497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137303, d138497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137304 q = 1) (hb : d138498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137304, d138498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137304, d138498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137305 q = 1) (hb : d138499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137305, d138499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137305, d138499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137306 q = 1) (hb : d138500 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137306, d138500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137306, d138500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24437 (p : Pattern) (ha : d137308 p = 1) (hb : d138502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52599 q = 1) (hb : d138484 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q hb ha
  have h3 (q : Pattern) (ha : d137291 q = 1) (hb : d138485 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137292 q = 1) (hb : d138486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137298 q = 1) (hb : d138492 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137298, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137298, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137307 q = 1) (hb : d138501 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137307, d138501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137307, d138501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137308 q = 1) (hb : d138502 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137308, d138502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137308, d138502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24438 (p : Pattern) (ha : d137314 p = 1) (hb : d138508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137301 q = 1) (hb : d138495 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137301, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24435 q ha hb
    | true =>
      simp only [d137301, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137302 q = 1) (hb : d138496 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137302, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137302, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137309 q = 1) (hb : d138503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137309, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24437 q ha hb
    | true =>
      simp only [d137309, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137310 q = 1) (hb : d138504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137310, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137310, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137311 q = 1) (hb : d138505 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137311, d138505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137311, d138505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137312 q = 1) (hb : d138506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137312, d138506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137312, d138506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137313 q = 1) (hb : d138507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137313, d138507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137313, d138507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137314 q = 1) (hb : d138508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137314, d138508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137314, d138508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24439 (p : Pattern) (ha : d5501 p = 1) (hb : d74225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d74221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d74177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d74222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d74178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d74223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d74224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5499 q = 1) (hb : d74225 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d74225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d74225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d74225 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5501 q = 1) (hb : d74225 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24440 (p : Pattern) (ha : d137326 p = 1) (hb : d138516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52594 q = 1) (hb : d138480 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q hb ha
  have h3 (q : Pattern) (ha : d137288 q = 1) (hb : d138481 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137288, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137288, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137289 q = 1) (hb : d138482 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137289, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137289, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52599 q = 1) (hb : d138484 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q hb ha
  have h7 (q : Pattern) (ha : d137291 q = 1) (hb : d138485 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137291, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137292 q = 1) (hb : d138486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137292, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137293 q = 1) (hb : d138487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137293, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137293, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74225 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74225 q = 1) (hb : d138511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24439 q hb ha
  have h12 (q : Pattern) (ha : d137322 q = 1) (hb : d138512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137322, d138512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137322, d138512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137323 q = 1) (hb : d138513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137323, d138513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137323, d138513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137324 q = 1) (hb : d138514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137324, d138514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137324, d138514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137325 q = 1) (hb : d138515 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137325, d138515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137325, d138515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137326 q = 1) (hb : d138516 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137326, d138516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137326, d138516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24441 (p : Pattern) (ha : d137332 p = 1) (hb : d138522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137327 q = 1) (hb : d138517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137327, d138517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24440 q ha hb
    | true =>
      simp only [d137327, d138517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137328 q = 1) (hb : d138518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137328, d138518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137328, d138518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137329 q = 1) (hb : d138519 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137329, d138519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137329, d138519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137330 q = 1) (hb : d138520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137330, d138520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137330, d138520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137331 q = 1) (hb : d138521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137331, d138521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137331, d138521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137332 q = 1) (hb : d138522 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137332, d138522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137332, d138522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24442 (p : Pattern) (ha : d137338 p = 1) (hb : d138528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137315 q = 1) (hb : d138509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137315, d138509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24436 q ha hb
    | true =>
      simp only [d137315, d138509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24438 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137321 q = 1) (hb : d138510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137321, d138510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137321, d138510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137333 q = 1) (hb : d138523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137333, d138523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24441 q ha hb
    | true =>
      simp only [d137333, d138523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137334 q = 1) (hb : d138524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137334, d138524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137334, d138524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137335 q = 1) (hb : d138525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137335, d138525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137335, d138525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137336 q = 1) (hb : d138526 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137336, d138526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137336, d138526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137337 q = 1) (hb : d138527 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137337, d138527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137337, d138527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137338 q = 1) (hb : d138528 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137338, d138528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137338, d138528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24443 (p : Pattern) (ha : d137319 p = 1) (hb : d138533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137309 q = 1) (hb : d138503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137309, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24437 q ha hb
    | true =>
      simp only [d137309, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137310 q = 1) (hb : d138504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137310, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137310, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137316 q = 1) (hb : d138530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137316, d138530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137316, d138530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137317 q = 1) (hb : d138531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137317, d138531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137317, d138531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137318 q = 1) (hb : d138532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137318, d138532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137318, d138532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137319 q = 1) (hb : d138533 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137319, d138533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137319, d138533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24444 (p : Pattern) (ha : d137345 p = 1) (hb : d138539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137340 q = 1) (hb : d138534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137340, d138534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24443 q ha hb
    | true =>
      simp only [d137340, d138534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137341 q = 1) (hb : d138535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137341, d138535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137341, d138535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137342 q = 1) (hb : d138536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137342, d138536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137342, d138536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137343 q = 1) (hb : d138537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137343, d138537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137343, d138537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137344 q = 1) (hb : d138538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137344, d138538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137344, d138538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137345 q = 1) (hb : d138539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137345, d138539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137345, d138539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24445 (p : Pattern) (ha : d137351 p = 1) (hb : d138545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137178 q = 1) (hb : d138367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137178, d138367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137178, d138367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24409 q ha hb
  have h2 (q : Pattern) (ha : d137179 q = 1) (hb : d138368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137179, d138368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137179, d138368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137188 q = 1) (hb : d138377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137188, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24409 q ha hb
    | true =>
      simp only [d137188, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24412 q ha hb
  have h4 (q : Pattern) (ha : d137189 q = 1) (hb : d138378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137189, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137189, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137190 q = 1) (hb : d138379 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137190, d138379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137190, d138379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137259 q = 1) (hb : d138450 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137259, d138450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24422 q ha hb
    | true =>
      simp only [d137259, d138450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24429 q ha hb
  have h7 (q : Pattern) (ha : d137272 q = 1) (hb : d138463 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137272, d138463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24430 q ha hb
    | true =>
      simp only [d137272, d138463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24431 q ha hb
  have h8 (q : Pattern) (ha : d137273 q = 1) (hb : d138464 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137273, d138464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137273, d138464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137274 q = 1) (hb : d138465 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137274, d138465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137274, d138465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d137275 q = 1) (hb : d138466 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137275, d138466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137275, d138466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137279 q = 1) (hb : d138470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137279, d138470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137279, d138470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24432 q ha hb
  have h12 (q : Pattern) (ha : d137281 q = 1) (hb : d138472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137281, d138472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137281, d138472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24433 q ha hb
  have h13 (q : Pattern) (ha : d137282 q = 1) (hb : d138473 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137282, d138473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137282, d138473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137283 q = 1) (hb : d138474 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137283, d138474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137283, d138474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137284 q = 1) (hb : d138475 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137284, d138475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d137284, d138475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d137285 q = 1) (hb : d138476 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137285, d138476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137285, d138476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137339 q = 1) (hb : d138529 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137339, d138529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137339, d138529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24442 q ha hb
  have h18 (q : Pattern) (ha : d137346 q = 1) (hb : d138540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137346, d138540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137346, d138540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24444 q ha hb
  have h19 (q : Pattern) (ha : d137347 q = 1) (hb : d138541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137347, d138541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137347, d138541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137348 q = 1) (hb : d138542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137348, d138542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137348, d138542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137349 q = 1) (hb : d138543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137349, d138543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d137349, d138543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d137350 q = 1) (hb : d138544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137350, d138544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137350, d138544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137351 q = 1) (hb : d138545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137351, d138545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137351, d138545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24446 (p : Pattern) (ha : d137357 p = 1) (hb : d138551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137352 q = 1) (hb : d138546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137352, d138546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137352, d138546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24445 q ha hb
  have h2 (q : Pattern) (ha : d137353 q = 1) (hb : d138547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137353, d138547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137353, d138547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137354 q = 1) (hb : d138548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137354, d138548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137354, d138548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137355 q = 1) (hb : d138549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137355, d138549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137355, d138549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137356 q = 1) (hb : d138550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137356, d138550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137356, d138550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137357 q = 1) (hb : d138551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137357, d138551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137357, d138551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24447 (p : Pattern) (ha : d137367 p = 1) (hb : d138563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52706 q = 1) (hb : d138554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q hb ha
  have h3 (q : Pattern) (ha : d137360 q = 1) (hb : d138555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137360, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137360, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137361 q = 1) (hb : d138556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137361, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137361, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52708 q = 1) (hb : d138557 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q hb ha
  have h7 (q : Pattern) (ha : d137362 q = 1) (hb : d138558 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137363 q = 1) (hb : d138559 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137364 q = 1) (hb : d138560 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137364, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137364, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137365 q = 1) (hb : d138561 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137365, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137365, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137366 q = 1) (hb : d138562 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137366, d138562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137366, d138562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137367 q = 1) (hb : d138563 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137367, d138563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137367, d138563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24448 (p : Pattern) (ha : d137371 p = 1) (hb : d138567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52708 q = 1) (hb : d138557 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q hb ha
  have h3 (q : Pattern) (ha : d137362 q = 1) (hb : d138558 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137363 q = 1) (hb : d138559 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137365 q = 1) (hb : d138561 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137365, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137365, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137370 q = 1) (hb : d138566 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137370, d138566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137370, d138566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137371 q = 1) (hb : d138567 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137371, d138567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137371, d138567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24449 (p : Pattern) (ha : d137377 p = 1) (hb : d138573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137374 q = 1) (hb : d138570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137375 q = 1) (hb : d138571 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137376 q = 1) (hb : d138572 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137376, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137376, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137377 q = 1) (hb : d138573 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137377, d138573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137377, d138573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24450 (p : Pattern) (ha : d137381 p = 1) (hb : d138577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d138574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d138575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137380 q = 1) (hb : d138576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137380, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137380, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137381 q = 1) (hb : d138577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137381, d138577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137381, d138577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24451 (p : Pattern) (ha : d137387 p = 1) (hb : d138583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137382 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
    | true =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
  have h2 (q : Pattern) (ha : d137383 q = 1) (hb : d138579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137383, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137383, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137384 q = 1) (hb : d138580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137384, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137384, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137385 q = 1) (hb : d138581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137385, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137385, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137386 q = 1) (hb : d138582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137386, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137386, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137387 q = 1) (hb : d138583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137387, d138583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137387, d138583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24452 (p : Pattern) (ha : d137390 p = 1) (hb : d138586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137374 q = 1) (hb : d138570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137375 q = 1) (hb : d138571 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137376 q = 1) (hb : d138572 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137376, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137376, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137390 q = 1) (hb : d138586 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137390, d138586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137390, d138586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24453 (p : Pattern) (ha : d137391 p = 1) (hb : d138587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d138574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d138575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137380 q = 1) (hb : d138576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137380, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137380, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137391 q = 1) (hb : d138587 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137391, d138587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137391, d138587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24454 (p : Pattern) (ha : d137397 p = 1) (hb : d138593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137382 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
    | true =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
  have h2 (q : Pattern) (ha : d137383 q = 1) (hb : d138579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137383, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137383, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137384 q = 1) (hb : d138580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137384, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137384, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137385 q = 1) (hb : d138581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137385, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137385, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137386 q = 1) (hb : d138582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137386, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137386, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137392 q = 1) (hb : d138588 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137392, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24452 q ha hb
    | true =>
      simp only [d137392, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24453 q ha hb
  have h7 (q : Pattern) (ha : d137393 q = 1) (hb : d138589 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137393, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137393, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137394 q = 1) (hb : d138590 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137394, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137394, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137395 q = 1) (hb : d138591 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137395, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137395, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137396 q = 1) (hb : d138592 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137396, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137396, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137397 q = 1) (hb : d138593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137397, d138593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137397, d138593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24455 (p : Pattern) (ha : d137402 p = 1) (hb : d138598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137374 q = 1) (hb : d138570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137375 q = 1) (hb : d138571 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137401 q = 1) (hb : d138597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137401, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137401, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137402 q = 1) (hb : d138598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137402, d138598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137402, d138598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24456 (p : Pattern) (ha : d137404 p = 1) (hb : d138600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d138574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d138575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137403 q = 1) (hb : d138599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137403, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137403, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137404 q = 1) (hb : d138600 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137404, d138600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137404, d138600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24457 (p : Pattern) (ha : d137411 p = 1) (hb : d138607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137374 q = 1) (hb : d138570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137409 q = 1) (hb : d138605 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137409, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137409, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137410 q = 1) (hb : d138606 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137410, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137410, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137411 q = 1) (hb : d138607 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137411, d138607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137411, d138607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24458 (p : Pattern) (ha : d137414 p = 1) (hb : d138610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d138574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137412 q = 1) (hb : d138608 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137412, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137412, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137413 q = 1) (hb : d138609 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137413, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137413, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137414 q = 1) (hb : d138610 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137414, d138610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137414, d138610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24459 (p : Pattern) (ha : d137422 p = 1) (hb : d138619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52695 q = 1) (hb : d138614 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12803 q hb ha
  have h3 (q : Pattern) (ha : d137418 q = 1) (hb : d138615 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137418, d138615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137418, d138615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137419 q = 1) (hb : d138616 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137419, d138616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137419, d138616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52706 q = 1) (hb : d138554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q hb ha
  have h7 (q : Pattern) (ha : d137360 q = 1) (hb : d138555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137360, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137360, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137361 q = 1) (hb : d138556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137361, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137361, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137420 q = 1) (hb : d138617 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137420, d138617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137420, d138617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52708 q = 1) (hb : d138557 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q hb ha
  have h12 (q : Pattern) (ha : d137362 q = 1) (hb : d138558 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137363 q = 1) (hb : d138559 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137364 q = 1) (hb : d138560 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137364, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137364, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137421 q = 1) (hb : d138618 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137421, d138618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137421, d138618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137422 q = 1) (hb : d138619 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137422, d138619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137422, d138619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24460 (p : Pattern) (ha : d137428 p = 1) (hb : d138625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137423 q = 1) (hb : d138620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137423, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24459 q ha hb
    | true =>
      simp only [d137423, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137424 q = 1) (hb : d138621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137424, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137424, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137425 q = 1) (hb : d138622 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137425, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137425, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137426 q = 1) (hb : d138623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137426, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137426, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137427 q = 1) (hb : d138624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137427, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137427, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137428 q = 1) (hb : d138625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137428, d138625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137428, d138625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24461 (p : Pattern) (ha : d5546 p = 1) (hb : d74270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5540 q = 1) (hb : d74266 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9275 q ha hb
    | true =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5541 q = 1) (hb : d74267 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5542 q = 1) (hb : d74268 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d74268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5542, d74268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5543 q = 1) (hb : d74269 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d74269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5543, d74269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5544 q = 1) (hb : d74270 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d74270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5544, d74270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74270 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5546 q = 1) (hb : d74270 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24462 (p : Pattern) (ha : d137435 p = 1) (hb : d138633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52706 q = 1) (hb : d138554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q hb ha
  have h3 (q : Pattern) (ha : d137360 q = 1) (hb : d138555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137360, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137360, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137361 q = 1) (hb : d138556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137361, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137361, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52708 q = 1) (hb : d138557 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q hb ha
  have h7 (q : Pattern) (ha : d137362 q = 1) (hb : d138558 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137362, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137363 q = 1) (hb : d138559 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137363, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137364 q = 1) (hb : d138560 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137364, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137364, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74270 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74270 q = 1) (hb : d138628 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24461 q hb ha
  have h12 (q : Pattern) (ha : d137431 q = 1) (hb : d138629 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137431, d138629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137431, d138629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137432 q = 1) (hb : d138630 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137432, d138630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137432, d138630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137433 q = 1) (hb : d138631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137433, d138631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137433, d138631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137434 q = 1) (hb : d138632 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137434, d138632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137434, d138632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137435 q = 1) (hb : d138633 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137435, d138633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137435, d138633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24463 (p : Pattern) (ha : d137441 p = 1) (hb : d138639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137436 q = 1) (hb : d138634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137436, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24462 q ha hb
    | true =>
      simp only [d137436, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137437 q = 1) (hb : d138635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137437, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137437, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137438 q = 1) (hb : d138636 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137438, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137438, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137439 q = 1) (hb : d138637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137439, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137439, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137440 q = 1) (hb : d138638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137440, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137440, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137441 q = 1) (hb : d138639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137441, d138639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137441, d138639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24464 (p : Pattern) (ha : d137447 p = 1) (hb : d138645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137405 q = 1) (hb : d138601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137405, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24455 q ha hb
    | true =>
      simp only [d137405, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24456 q ha hb
  have h2 (q : Pattern) (ha : d137406 q = 1) (hb : d138602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137406, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137406, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137407 q = 1) (hb : d138603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137407, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137407, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137408 q = 1) (hb : d138604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137408, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137408, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137415 q = 1) (hb : d138611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137415, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24457 q ha hb
    | true =>
      simp only [d137415, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24458 q ha hb
  have h6 (q : Pattern) (ha : d137416 q = 1) (hb : d138612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137416, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137416, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137417 q = 1) (hb : d138613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137417, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137417, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137429 q = 1) (hb : d138626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137429, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24460 q ha hb
    | true =>
      simp only [d137429, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137430 q = 1) (hb : d138627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137430, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137430, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137442 q = 1) (hb : d138640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137442, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24463 q ha hb
    | true =>
      simp only [d137442, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137443 q = 1) (hb : d138641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137443, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137443, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137444 q = 1) (hb : d138642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137444, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137444, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137445 q = 1) (hb : d138643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137445, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137445, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137446 q = 1) (hb : d138644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137446, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137446, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137447 q = 1) (hb : d138645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137447, d138645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137447, d138645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24465 (p : Pattern) (ha : d137448 p = 1) (hb : d138646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137374 q = 1) (hb : d138570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137375 q = 1) (hb : d138571 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137375, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137401 q = 1) (hb : d138597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137401, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137401, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137448 q = 1) (hb : d138646 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137448, d138646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137448, d138646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24466 (p : Pattern) (ha : d137449 p = 1) (hb : d138647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d138574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d138575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137403 q = 1) (hb : d138599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137403, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137403, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137449 q = 1) (hb : d138647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137449, d138647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137449, d138647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24467 (p : Pattern) (ha : d137454 p = 1) (hb : d138652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137374 q = 1) (hb : d138570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137374, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137409 q = 1) (hb : d138605 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137409, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137409, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137410 q = 1) (hb : d138606 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137410, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137410, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137454 q = 1) (hb : d138652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137454, d138652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137454, d138652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24468 (p : Pattern) (ha : d137455 p = 1) (hb : d138653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d138568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24448 q ha hb
    | true =>
      simp only [d137372, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d138569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d138574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137412 q = 1) (hb : d138608 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137412, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137412, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137413 q = 1) (hb : d138609 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137413, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137413, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137455 q = 1) (hb : d138653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137455, d138653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137455, d138653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24469 (p : Pattern) (ha : d137459 p = 1) (hb : d138657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137423 q = 1) (hb : d138620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137423, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24459 q ha hb
    | true =>
      simp only [d137423, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137424 q = 1) (hb : d138621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137424, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137424, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137368 q = 1) (hb : d138564 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24447 q ha hb
    | true =>
      simp only [d137368, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137369 q = 1) (hb : d138565 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137369, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137425 q = 1) (hb : d138622 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137425, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137425, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137426 q = 1) (hb : d138623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137426, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137426, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137427 q = 1) (hb : d138624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137427, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137427, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137459 q = 1) (hb : d138657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137459, d138657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137459, d138657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24470 (p : Pattern) (ha : d137462 p = 1) (hb : d138660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137436 q = 1) (hb : d138634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137436, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24462 q ha hb
    | true =>
      simp only [d137436, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137437 q = 1) (hb : d138635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137437, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137437, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137438 q = 1) (hb : d138636 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137438, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137438, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137439 q = 1) (hb : d138637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137439, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137439, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137440 q = 1) (hb : d138638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137440, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137440, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137462 q = 1) (hb : d138660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137462, d138660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137462, d138660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24471 (p : Pattern) (ha : d137468 p = 1) (hb : d138666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137405 q = 1) (hb : d138601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137405, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24455 q ha hb
    | true =>
      simp only [d137405, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24456 q ha hb
  have h2 (q : Pattern) (ha : d137406 q = 1) (hb : d138602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137406, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137406, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137407 q = 1) (hb : d138603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137407, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137407, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137408 q = 1) (hb : d138604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137408, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137408, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137415 q = 1) (hb : d138611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137415, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24457 q ha hb
    | true =>
      simp only [d137415, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24458 q ha hb
  have h6 (q : Pattern) (ha : d137416 q = 1) (hb : d138612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137416, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137416, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137417 q = 1) (hb : d138613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137417, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137417, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137429 q = 1) (hb : d138626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137429, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24460 q ha hb
    | true =>
      simp only [d137429, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137430 q = 1) (hb : d138627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137430, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137430, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137442 q = 1) (hb : d138640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137442, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24463 q ha hb
    | true =>
      simp only [d137442, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137443 q = 1) (hb : d138641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137443, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137443, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137444 q = 1) (hb : d138642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137444, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137444, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137445 q = 1) (hb : d138643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137445, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137445, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137446 q = 1) (hb : d138644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137446, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137446, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137450 q = 1) (hb : d138648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137450, d138648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24465 q ha hb
    | true =>
      simp only [d137450, d138648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24466 q ha hb
  have h17 (q : Pattern) (ha : d137451 q = 1) (hb : d138649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137451, d138649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137451, d138649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137452 q = 1) (hb : d138650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137452, d138650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137452, d138650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137453 q = 1) (hb : d138651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137453, d138651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137453, d138651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137456 q = 1) (hb : d138654 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137456, d138654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24467 q ha hb
    | true =>
      simp only [d137456, d138654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24468 q ha hb
  have h21 (q : Pattern) (ha : d137457 q = 1) (hb : d138655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137457, d138655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137457, d138655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137458 q = 1) (hb : d138656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137458, d138656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137458, d138656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137460 q = 1) (hb : d138658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137460, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24469 q ha hb
    | true =>
      simp only [d137460, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24452 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d137392 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d137461 q = 1) (hb : d138659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137461, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d137461, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d137463 q = 1) (hb : d138661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137463, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24470 q ha hb
    | true =>
      simp only [d137463, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d137464 q = 1) (hb : d138662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137464, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d137464, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d137465 q = 1) (hb : d138663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137465, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d137465, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d137466 q = 1) (hb : d138664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137466, d138664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d137466, d138664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d137467 q = 1) (hb : d138665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137467, d138665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137467, d138665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d137468 q = 1) (hb : d138666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137468, d138666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137468, d138666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24472 (p : Pattern) (ha : d137475 p = 1) (hb : d138673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137382 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
    | true =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
  have h2 (q : Pattern) (ha : d137383 q = 1) (hb : d138579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137383, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137383, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137384 q = 1) (hb : d138580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137384, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137384, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137385 q = 1) (hb : d138581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137385, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137385, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137386 q = 1) (hb : d138582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137386, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137386, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137470 q = 1) (hb : d138668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137470, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
    | true =>
      simp only [d137470, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137471 q = 1) (hb : d138669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137471, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137471, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137472 q = 1) (hb : d138670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137472, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137472, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137473 q = 1) (hb : d138671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137473, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137473, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137474 q = 1) (hb : d138672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137474, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137474, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137475 q = 1) (hb : d138673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137475, d138673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137475, d138673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24473 (p : Pattern) (ha : d137481 p = 1) (hb : d138679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137470 q = 1) (hb : d138668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137470, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
    | true =>
      simp only [d137470, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137471 q = 1) (hb : d138669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137471, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137471, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137472 q = 1) (hb : d138670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137472, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137472, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137473 q = 1) (hb : d138671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137473, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137473, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137474 q = 1) (hb : d138672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137474, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137474, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137476 q = 1) (hb : d138674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137476, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24453 q ha hb
    | true =>
      simp only [d137476, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137477 q = 1) (hb : d138675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137477, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137477, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137478 q = 1) (hb : d138676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137478, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137478, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137479 q = 1) (hb : d138677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137479, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137479, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137480 q = 1) (hb : d138678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137480, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137480, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137481 q = 1) (hb : d138679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137481, d138679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137481, d138679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24474 (p : Pattern) (ha : d137488 p = 1) (hb : d138686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137460 q = 1) (hb : d138658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137460, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24469 q ha hb
    | true =>
      simp only [d137460, d138658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24452 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137392 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137461 q = 1) (hb : d138659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137461, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137461, d138659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137463 q = 1) (hb : d138661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137463, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24470 q ha hb
    | true =>
      simp only [d137463, d138661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137464 q = 1) (hb : d138662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137464, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137464, d138662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137465 q = 1) (hb : d138663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137465, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137465, d138663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137486 q = 1) (hb : d138684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137486, d138684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137486, d138684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137487 q = 1) (hb : d138685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137487, d138685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137487, d138685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137488 q = 1) (hb : d138686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137488, d138686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137488, d138686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24475 (p : Pattern) (ha : d137490 p = 1) (hb : d138688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137476 q = 1) (hb : d138674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137476, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24453 q ha hb
    | true =>
      simp only [d137476, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137477 q = 1) (hb : d138675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137477, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137477, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137478 q = 1) (hb : d138676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137478, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137478, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137479 q = 1) (hb : d138677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137479, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137479, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137480 q = 1) (hb : d138678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137480, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137480, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137490 q = 1) (hb : d138688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137490, d138688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137490, d138688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24476 (p : Pattern) (ha : d137505 p = 1) (hb : d138706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52877 q = 1) (hb : d138694 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12819 q hb ha
  have h3 (q : Pattern) (ha : d137496 q = 1) (hb : d138695 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137496, d138695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137496, d138695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137497 q = 1) (hb : d138696 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137497, d138696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137497, d138696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52883 q = 1) (hb : d138697 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q hb ha
  have h7 (q : Pattern) (ha : d137498 q = 1) (hb : d138698 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137498, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137498, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137499 q = 1) (hb : d138699 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137499, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137499, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137500 q = 1) (hb : d138700 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137500, d138700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137500, d138700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52888 q = 1) (hb : d138701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q hb ha
  have h12 (q : Pattern) (ha : d137501 q = 1) (hb : d138702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137502 q = 1) (hb : d138703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137503 q = 1) (hb : d138704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137503, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137503, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137504 q = 1) (hb : d138705 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137504, d138705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137504, d138705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137505 q = 1) (hb : d138706 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137505, d138706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137505, d138706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24477 (p : Pattern) (ha : d137510 p = 1) (hb : d138711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52883 q = 1) (hb : d138697 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q hb ha
  have h3 (q : Pattern) (ha : d137498 q = 1) (hb : d138698 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137498, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137498, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137499 q = 1) (hb : d138699 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137499, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137499, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52888 q = 1) (hb : d138701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q hb ha
  have h7 (q : Pattern) (ha : d137501 q = 1) (hb : d138702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137502 q = 1) (hb : d138703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137503 q = 1) (hb : d138704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137503, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137503, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137508 q = 1) (hb : d138709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137508, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137508, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137509 q = 1) (hb : d138710 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137509, d138710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137509, d138710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137510 q = 1) (hb : d138711 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137510, d138711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137510, d138711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24478 (p : Pattern) (ha : d137516 p = 1) (hb : d138717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137506 q = 1) (hb : d138707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137506, d138707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24476 q ha hb
    | true =>
      simp only [d137506, d138707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137507 q = 1) (hb : d138708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137507, d138708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137507, d138708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137511 q = 1) (hb : d138712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137511, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24477 q ha hb
    | true =>
      simp only [d137511, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137512 q = 1) (hb : d138713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137512, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137512, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137513 q = 1) (hb : d138714 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137513, d138714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137513, d138714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137514 q = 1) (hb : d138715 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137514, d138715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137514, d138715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137515 q = 1) (hb : d138716 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137515, d138716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137515, d138716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137516 q = 1) (hb : d138717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137516, d138717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137516, d138717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24479 (p : Pattern) (ha : d137518 p = 1) (hb : d138719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52888 q = 1) (hb : d138701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q hb ha
  have h3 (q : Pattern) (ha : d137501 q = 1) (hb : d138702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137502 q = 1) (hb : d138703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137508 q = 1) (hb : d138709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137508, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137508, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137517 q = 1) (hb : d138718 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137517, d138718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137517, d138718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137518 q = 1) (hb : d138719 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137518, d138719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137518, d138719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24480 (p : Pattern) (ha : d137524 p = 1) (hb : d138725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137511 q = 1) (hb : d138712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137511, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24477 q ha hb
    | true =>
      simp only [d137511, d138712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137512 q = 1) (hb : d138713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137512, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137512, d138713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137519 q = 1) (hb : d138720 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137519, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24479 q ha hb
    | true =>
      simp only [d137519, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137520 q = 1) (hb : d138721 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137520, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137520, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137521 q = 1) (hb : d138722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137521, d138722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137521, d138722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137522 q = 1) (hb : d138723 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137522, d138723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137522, d138723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137523 q = 1) (hb : d138724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137523, d138724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137523, d138724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137524 q = 1) (hb : d138725 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137524, d138725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137524, d138725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24481 (p : Pattern) (ha : d5590 p = 1) (hb : d74314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5584 q = 1) (hb : d74310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d74310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5584, d74310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9275 q ha hb
  have h2 (q : Pattern) (ha : d5540 q = 1) (hb : d74266 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9275 q ha hb
    | true =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5585 q = 1) (hb : d74311 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d74311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5585, d74311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5541 q = 1) (hb : d74267 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5586 q = 1) (hb : d74312 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d74312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5586, d74312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5587 q = 1) (hb : d74313 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d74313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5587, d74313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5588 q = 1) (hb : d74314 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, d74314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5588, d74314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d74314 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5590 q = 1) (hb : d74314 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24482 (p : Pattern) (ha : d137536 p = 1) (hb : d138733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52883 q = 1) (hb : d138697 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q hb ha
  have h3 (q : Pattern) (ha : d137498 q = 1) (hb : d138698 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137498, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137498, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137499 q = 1) (hb : d138699 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137499, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137499, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52888 q = 1) (hb : d138701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q hb ha
  have h7 (q : Pattern) (ha : d137501 q = 1) (hb : d138702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137501, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137502 q = 1) (hb : d138703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137502, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137503 q = 1) (hb : d138704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137503, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137503, d138704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74314 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74314 q = 1) (hb : d138728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24481 q hb ha
  have h12 (q : Pattern) (ha : d137532 q = 1) (hb : d138729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137532, d138729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137532, d138729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137533 q = 1) (hb : d138730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137533, d138730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137533, d138730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137534 q = 1) (hb : d138731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137534, d138731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137534, d138731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137535 q = 1) (hb : d138732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137535, d138732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137535, d138732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137536 q = 1) (hb : d138733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137536, d138733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137536, d138733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24483 (p : Pattern) (ha : d137542 p = 1) (hb : d138739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137537 q = 1) (hb : d138734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137537, d138734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24482 q ha hb
    | true =>
      simp only [d137537, d138734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137538 q = 1) (hb : d138735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137538, d138735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137538, d138735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137539 q = 1) (hb : d138736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137539, d138736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137539, d138736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137540 q = 1) (hb : d138737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137540, d138737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137540, d138737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137541 q = 1) (hb : d138738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137541, d138738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137541, d138738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137542 q = 1) (hb : d138739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137542, d138739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137542, d138739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24484 (p : Pattern) (ha : d137548 p = 1) (hb : d138745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137525 q = 1) (hb : d138726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137525, d138726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24478 q ha hb
    | true =>
      simp only [d137525, d138726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24480 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137531 q = 1) (hb : d138727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137531, d138727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137531, d138727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137543 q = 1) (hb : d138740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137543, d138740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24483 q ha hb
    | true =>
      simp only [d137543, d138740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137544 q = 1) (hb : d138741 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137544, d138741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137544, d138741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137545 q = 1) (hb : d138742 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137545, d138742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137545, d138742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137546 q = 1) (hb : d138743 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137546, d138743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137546, d138743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137547 q = 1) (hb : d138744 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137547, d138744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137547, d138744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137548 q = 1) (hb : d138745 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137548, d138745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137548, d138745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24485 (p : Pattern) (ha : d137529 p = 1) (hb : d138750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137519 q = 1) (hb : d138720 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137519, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24479 q ha hb
    | true =>
      simp only [d137519, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137520 q = 1) (hb : d138721 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137520, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137520, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137526 q = 1) (hb : d138747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137526, d138747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137526, d138747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137527 q = 1) (hb : d138748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137527, d138748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137527, d138748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137528 q = 1) (hb : d138749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137528, d138749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137528, d138749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137529 q = 1) (hb : d138750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137529, d138750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137529, d138750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24486 (p : Pattern) (ha : d137555 p = 1) (hb : d138756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137550 q = 1) (hb : d138751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137550, d138751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24485 q ha hb
    | true =>
      simp only [d137550, d138751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137551 q = 1) (hb : d138752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137551, d138752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137551, d138752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137552 q = 1) (hb : d138753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137552, d138753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137552, d138753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137553 q = 1) (hb : d138754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137553, d138754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137553, d138754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137554 q = 1) (hb : d138755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137554, d138755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137554, d138755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137555 q = 1) (hb : d138756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137555, d138756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137555, d138756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24487 (p : Pattern) (ha : d137561 p = 1) (hb : d138762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137388 q = 1) (hb : d138584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137388, d138584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137388, d138584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24451 q ha hb
  have h2 (q : Pattern) (ha : d137389 q = 1) (hb : d138585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137389, d138585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137389, d138585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137398 q = 1) (hb : d138594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137398, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24451 q ha hb
    | true =>
      simp only [d137398, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24454 q ha hb
  have h4 (q : Pattern) (ha : d137399 q = 1) (hb : d138595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137399, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137399, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137400 q = 1) (hb : d138596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137400, d138596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137400, d138596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137469 q = 1) (hb : d138667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137469, d138667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24464 q ha hb
    | true =>
      simp only [d137469, d138667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24471 q ha hb
  have h7 (q : Pattern) (ha : d137482 q = 1) (hb : d138680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137482, d138680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24472 q ha hb
    | true =>
      simp only [d137482, d138680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24473 q ha hb
  have h8 (q : Pattern) (ha : d137483 q = 1) (hb : d138681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137483, d138681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137483, d138681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137484 q = 1) (hb : d138682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137484, d138682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137484, d138682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d137485 q = 1) (hb : d138683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137485, d138683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137485, d138683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137489 q = 1) (hb : d138687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137489, d138687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137489, d138687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24474 q ha hb
  have h12 (q : Pattern) (ha : d137491 q = 1) (hb : d138689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137491, d138689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137491, d138689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24475 q ha hb
  have h13 (q : Pattern) (ha : d137492 q = 1) (hb : d138690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137492, d138690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137492, d138690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137493 q = 1) (hb : d138691 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137493, d138691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137493, d138691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137494 q = 1) (hb : d138692 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137494, d138692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d137494, d138692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d137495 q = 1) (hb : d138693 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137495, d138693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137495, d138693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137549 q = 1) (hb : d138746 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137549, d138746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137549, d138746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24484 q ha hb
  have h18 (q : Pattern) (ha : d137556 q = 1) (hb : d138757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137556, d138757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137556, d138757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24486 q ha hb
  have h19 (q : Pattern) (ha : d137557 q = 1) (hb : d138758 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137557, d138758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137557, d138758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137558 q = 1) (hb : d138759 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137558, d138759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137558, d138759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137559 q = 1) (hb : d138760 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137559, d138760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d137559, d138760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d137560 q = 1) (hb : d138761 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137560, d138761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137560, d138761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137561 q = 1) (hb : d138762 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137561, d138762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137561, d138762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24488 (p : Pattern) (ha : d137567 p = 1) (hb : d138768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137562 q = 1) (hb : d138763 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137562, d138763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137562, d138763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24487 q ha hb
  have h2 (q : Pattern) (ha : d137563 q = 1) (hb : d138764 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137563, d138764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137563, d138764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137564 q = 1) (hb : d138765 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137564, d138765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137564, d138765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137565 q = 1) (hb : d138766 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137565, d138766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137565, d138766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137566 q = 1) (hb : d138767 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137566, d138767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137566, d138767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137567 q = 1) (hb : d138768 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137567, d138768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137567, d138768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24489 (p : Pattern) (ha : d137578 p = 1) (hb : d138781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53027 q = 1) (hb : d138772 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q hb ha
  have h3 (q : Pattern) (ha : d137571 q = 1) (hb : d138773 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137571, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137571, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137572 q = 1) (hb : d138774 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137572, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137572, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53029 q = 1) (hb : d138775 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q hb ha
  have h7 (q : Pattern) (ha : d137573 q = 1) (hb : d138776 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137574 q = 1) (hb : d138777 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137575 q = 1) (hb : d138778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137575, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137575, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137576 q = 1) (hb : d138779 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137576, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137576, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137577 q = 1) (hb : d138780 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137577, d138780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137577, d138780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137578 q = 1) (hb : d138781 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137578, d138781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137578, d138781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24490 (p : Pattern) (ha : d137582 p = 1) (hb : d138785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53029 q = 1) (hb : d138775 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q hb ha
  have h3 (q : Pattern) (ha : d137573 q = 1) (hb : d138776 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137574 q = 1) (hb : d138777 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137576 q = 1) (hb : d138779 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137576, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137576, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137581 q = 1) (hb : d138784 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137581, d138784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137581, d138784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137582 q = 1) (hb : d138785 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137582, d138785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137582, d138785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24491 (p : Pattern) (ha : d137588 p = 1) (hb : d138791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137585 q = 1) (hb : d138788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137586 q = 1) (hb : d138789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137587 q = 1) (hb : d138790 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137587, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137587, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137588 q = 1) (hb : d138791 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137588, d138791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137588, d138791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24492 (p : Pattern) (ha : d137592 p = 1) (hb : d138795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d138792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d138793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137591 q = 1) (hb : d138794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137591, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137591, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137592 q = 1) (hb : d138795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137592, d138795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137592, d138795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24493 (p : Pattern) (ha : d137598 p = 1) (hb : d138801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137593 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
    | true =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
  have h2 (q : Pattern) (ha : d137594 q = 1) (hb : d138797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137594, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137594, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137595 q = 1) (hb : d138798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137595, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137595, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137596 q = 1) (hb : d138799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137596, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137596, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137597 q = 1) (hb : d138800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137597, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137597, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137598 q = 1) (hb : d138801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137598, d138801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137598, d138801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24494 (p : Pattern) (ha : d137601 p = 1) (hb : d138804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137585 q = 1) (hb : d138788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137586 q = 1) (hb : d138789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137587 q = 1) (hb : d138790 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137587, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137587, d138790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137601 q = 1) (hb : d138804 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137601, d138804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137601, d138804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24495 (p : Pattern) (ha : d137602 p = 1) (hb : d138805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d138792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d138793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137591 q = 1) (hb : d138794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137591, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137591, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137602 q = 1) (hb : d138805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137602, d138805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137602, d138805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24496 (p : Pattern) (ha : d137608 p = 1) (hb : d138811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137593 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
    | true =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
  have h2 (q : Pattern) (ha : d137594 q = 1) (hb : d138797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137594, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137594, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137595 q = 1) (hb : d138798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137595, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137595, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137596 q = 1) (hb : d138799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137596, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137596, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137597 q = 1) (hb : d138800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137597, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137597, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137603 q = 1) (hb : d138806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137603, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24494 q ha hb
    | true =>
      simp only [d137603, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24495 q ha hb
  have h7 (q : Pattern) (ha : d137604 q = 1) (hb : d138807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137604, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137604, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137605 q = 1) (hb : d138808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137605, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137605, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137606 q = 1) (hb : d138809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137606, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137606, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137607 q = 1) (hb : d138810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137607, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137607, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137608 q = 1) (hb : d138811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137608, d138811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137608, d138811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24497 (p : Pattern) (ha : d137613 p = 1) (hb : d138816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137585 q = 1) (hb : d138788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137586 q = 1) (hb : d138789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137612 q = 1) (hb : d138815 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137612, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137612, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137613 q = 1) (hb : d138816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137613, d138816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137613, d138816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24498 (p : Pattern) (ha : d137615 p = 1) (hb : d138818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d138792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d138793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137614 q = 1) (hb : d138817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137614, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137614, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137615 q = 1) (hb : d138818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137615, d138818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137615, d138818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24499 (p : Pattern) (ha : d137622 p = 1) (hb : d138825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137585 q = 1) (hb : d138788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137620 q = 1) (hb : d138823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137620, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137620, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137621 q = 1) (hb : d138824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137621, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137621, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137622 q = 1) (hb : d138825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137622, d138825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137622, d138825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
