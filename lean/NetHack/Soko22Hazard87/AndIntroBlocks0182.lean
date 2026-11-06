import NetHack.Soko22Hazard87.AndIntroBlocks0181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro45500 (p : Pattern) (ha : d181561 p = 1) (hb : d194103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181556 q = 1) (hb : d194098 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181556, d194098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181556, d194098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45499 q ha hb
  have h2 (q : Pattern) (ha : d181557 q = 1) (hb : d194099 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181557, d194099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181557, d194099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181558 q = 1) (hb : d194100 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181558, d194100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181558, d194100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181559 q = 1) (hb : d194101 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181559, d194101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181559, d194101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181560 q = 1) (hb : d194102 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181560, d194102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181560, d194102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181561 q = 1) (hb : d194103 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181561, d194103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181561, d194103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45501 (p : Pattern) (ha : d181567 p = 1) (hb : d194109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d181096 q = 1) (hb : d193772 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181096, d193772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45414 q ha hb
    | true =>
      simp only [d181096, d193772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45427 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181185 q = 1) (hb : d193840 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181185, d193840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181185, d193840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45443 q ha hb
  have h3 (q : Pattern) (ha : d181186 q = 1) (hb : d193841 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181186, d193841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181186, d193841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181310 q = 1) (hb : d193927 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181310, d193927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181310, d193927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45462 q ha hb
  have h5 (q : Pattern) (ha : d181311 q = 1) (hb : d193928 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181311, d193928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181311, d193928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181312 q = 1) (hb : d193929 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181312, d193929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181312, d193929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181438 q = 1) (hb : d194015 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181438, d194015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181438, d194015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45481 q ha hb
  have h8 (q : Pattern) (ha : d181439 q = 1) (hb : d194016 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181439, d194016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181439, d194016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d181440 q = 1) (hb : d194017 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181440, d194017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181440, d194017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181441 q = 1) (hb : d194018 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d181441, d194018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181441, d194018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181562 q = 1) (hb : d194104 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181562, d194104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181562, d194104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45500 q ha hb
  have h12 (q : Pattern) (ha : d181563 q = 1) (hb : d194105 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181563, d194105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181563, d194105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d181564 q = 1) (hb : d194106 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181564, d194106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181564, d194106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d181565 q = 1) (hb : d194107 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d181565, d194107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181565, d194107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d181566 q = 1) (hb : d194108 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d181566, d194108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d181566, d194108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d181567 q = 1) (hb : d194109 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d181567, d194109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d181567, d194109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro45502 (p : Pattern) (ha : d181573 p = 1) (hb : d194115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181568 q = 1) (hb : d194110 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d181568, d194110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45501 q ha hb
    | true =>
      simp only [d181568, d194110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181569 q = 1) (hb : d194111 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d181569, d194111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181569, d194111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181570 q = 1) (hb : d194112 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d181570, d194112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181570, d194112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181571 q = 1) (hb : d194113 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d181571, d194113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181571, d194113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181572 q = 1) (hb : d194114 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d181572, d194114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181572, d194114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181573 q = 1) (hb : d194115 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d181573, d194115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181573, d194115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45503 (p : Pattern) (ha : d181579 p = 1) (hb : d194121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181574 q = 1) (hb : d194116 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d181574, d194116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45502 q ha hb
    | true =>
      simp only [d181574, d194116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181575 q = 1) (hb : d194117 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d181575, d194117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181575, d194117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181576 q = 1) (hb : d194118 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d181576, d194118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181576, d194118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181577 q = 1) (hb : d194119 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d181577, d194119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181577, d194119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181578 q = 1) (hb : d194120 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d181578, d194120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181578, d194120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181579 q = 1) (hb : d194121 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d181579, d194121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181579, d194121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45504 (p : Pattern) (ha : d181585 p = 1) (hb : d194127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181580 q = 1) (hb : d194122 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d181580, d194122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45503 q ha hb
    | true =>
      simp only [d181580, d194122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181581 q = 1) (hb : d194123 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d181581, d194123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181581, d194123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181582 q = 1) (hb : d194124 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d181582, d194124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181582, d194124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181583 q = 1) (hb : d194125 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d181583, d194125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181583, d194125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181584 q = 1) (hb : d194126 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d181584, d194126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181584, d194126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181585 q = 1) (hb : d194127 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d181585, d194127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181585, d194127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45505 (p : Pattern) (ha : d181591 p = 1) (hb : d194133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181586 q = 1) (hb : d194128 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d181586, d194128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45504 q ha hb
    | true =>
      simp only [d181586, d194128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181587 q = 1) (hb : d194129 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d181587, d194129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181587, d194129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181588 q = 1) (hb : d194130 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d181588, d194130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181588, d194130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181589 q = 1) (hb : d194131 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d181589, d194131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181589, d194131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181590 q = 1) (hb : d194132 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d181590, d194132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181590, d194132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181591 q = 1) (hb : d194133 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d181591, d194133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181591, d194133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45506 (p : Pattern) (ha : d181597 p = 1) (hb : d194139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181592 q = 1) (hb : d194134 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d181592, d194134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45505 q ha hb
    | true =>
      simp only [d181592, d194134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181593 q = 1) (hb : d194135 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d181593, d194135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181593, d194135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181594 q = 1) (hb : d194136 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d181594, d194136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181594, d194136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181595 q = 1) (hb : d194137 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d181595, d194137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181595, d194137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181596 q = 1) (hb : d194138 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d181596, d194138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181596, d194138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181597 q = 1) (hb : d194139 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d181597, d194139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181597, d194139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45507 (p : Pattern) (ha : d181603 p = 1) (hb : d194145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181598 q = 1) (hb : d194140 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d181598, d194140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45506 q ha hb
    | true =>
      simp only [d181598, d194140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181599 q = 1) (hb : d194141 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d181599, d194141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181599, d194141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181600 q = 1) (hb : d194142 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d181600, d194142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181600, d194142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181601 q = 1) (hb : d194143 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d181601, d194143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181601, d194143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181602 q = 1) (hb : d194144 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d181602, d194144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181602, d194144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181603 q = 1) (hb : d194145 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d181603, d194145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181603, d194145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45508 (p : Pattern) (ha : d181609 p = 1) (hb : d194151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181604 q = 1) (hb : d194146 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d181604, d194146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45507 q ha hb
    | true =>
      simp only [d181604, d194146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181605 q = 1) (hb : d194147 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d181605, d194147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181605, d194147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181606 q = 1) (hb : d194148 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d181606, d194148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181606, d194148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181607 q = 1) (hb : d194149 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d181607, d194149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181607, d194149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181608 q = 1) (hb : d194150 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d181608, d194150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181608, d194150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181609 q = 1) (hb : d194151 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d181609, d194151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181609, d194151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45509 (p : Pattern) (ha : d188486 p = 1) (hb : d192722 p = 1) : d181614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d188486 q = 1) : d181011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45266 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192718 q = 1) : d181610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192718, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192718, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192719 q = 1) : d181611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192719, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192719, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192720 q = 1) : d181612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192720, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192720, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192721 q = 1) : d181613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192721, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192721, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192722 q = 1) : d181614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192722, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192722, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45510 (p : Pattern) (ha : d188486 p = 1) (hb : d192732 p = 1) : d181624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d188486 q = 1) : d180957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45263 q ha hb
    | true =>
      simp only [d20420, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45257 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192728 q = 1) : d181620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192728, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192728, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192729 q = 1) : d181621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192729, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192729, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192730 q = 1) : d181622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192730, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192730, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192731 q = 1) : d181623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192731, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192731, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192732 q = 1) : d181624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192732, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192732, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45511 (p : Pattern) (ha : d188486 p = 1) (hb : d192738 p = 1) : d181630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192733 q = 1) : d181625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192733, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192733, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45510 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192734 q = 1) : d181626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192734, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192734, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192735 q = 1) : d181627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192735, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192735, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192736 q = 1) : d181628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192736, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192736, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192737 q = 1) : d181629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192737, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192737, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192738 q = 1) : d181630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192738, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192738, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45512 (p : Pattern) (ha : d188486 p = 1) (hb : d192744 p = 1) : d181636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192723 q = 1) : d181615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192723, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192723, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45509 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192724 q = 1) : d181616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192724, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192724, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192725 q = 1) : d181617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192725, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192725, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192726 q = 1) : d181618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192726, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192726, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192727 q = 1) : d181619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192727, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192727, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192739 q = 1) : d181631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192739, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192739, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45511 q ha hb
  have h7 (q : Pattern) (ha : d188486 q = 1) (hb : d192740 q = 1) : d181632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192740, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192740, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d188486 q = 1) (hb : d192741 q = 1) : d181633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192741, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192741, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d188486 q = 1) (hb : d192742 q = 1) : d181634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192742, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192742, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d188486 q = 1) (hb : d192743 q = 1) : d181635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192743, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192743, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d188486 q = 1) (hb : d192744 q = 1) : d181636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192744, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192744, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45513 (p : Pattern) (ha : d188486 p = 1) (hb : d192750 p = 1) : d181642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192745 q = 1) : d181637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192745, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45285 q hb ha
    | true =>
      simp only [d192745, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45276 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192746 q = 1) : d181638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192746, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192746, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192747 q = 1) : d181639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192747, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192747, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192748 q = 1) : d181640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192748, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192748, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192749 q = 1) : d181641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192749, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192749, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192750 q = 1) : d181642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192750, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192750, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45514 (p : Pattern) (ha : d188486 p = 1) (hb : d192756 p = 1) : d181648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192751 q = 1) : d181643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192751, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192751, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45513 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192752 q = 1) : d181644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192752, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192752, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192753 q = 1) : d181645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192753, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192753, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192754 q = 1) : d181646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192754, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192754, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192755 q = 1) : d181647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192755, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192755, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192756 q = 1) : d181648 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192756, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192756, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45515 (p : Pattern) (ha : d188486 p = 1) (hb : d192762 p = 1) : d181654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192757 q = 1) : d181649 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192757, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192757, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45514 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192758 q = 1) : d181650 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192758, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192758, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192759 q = 1) : d181651 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192759, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192759, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192760 q = 1) : d181652 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192760, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192760, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192761 q = 1) : d181653 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192761, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192761, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192762 q = 1) : d181654 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192762, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192762, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45516 (p : Pattern) (ha : d188486 p = 1) (hb : d192769 p = 1) : d181661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192764 q = 1) : d181656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192764, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45306 q hb ha
    | true =>
      simp only [d192764, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45295 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192765 q = 1) : d181657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192765, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192765, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192766 q = 1) : d181658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192766, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192766, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192767 q = 1) : d181659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192767, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192767, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192768 q = 1) : d181660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192768, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192768, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192769 q = 1) : d181661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192769, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192769, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45517 (p : Pattern) (ha : d188486 p = 1) (hb : d192775 p = 1) : d181667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192770 q = 1) : d181662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192770, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192770, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45516 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192771 q = 1) : d181663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192771, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192771, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192772 q = 1) : d181664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192772, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192772, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192773 q = 1) : d181665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192773, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192773, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192774 q = 1) : d181666 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192774, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192774, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192775 q = 1) : d181667 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192775, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192775, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45518 (p : Pattern) (ha : d188486 p = 1) (hb : d192781 p = 1) : d181673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192776 q = 1) : d181668 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192776, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192776, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45517 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192777 q = 1) : d181669 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192777, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192777, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192778 q = 1) : d181670 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192778, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192778, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192779 q = 1) : d181671 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192779, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192779, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192780 q = 1) : d181672 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192780, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192780, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192781 q = 1) : d181673 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192781, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192781, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45519 (p : Pattern) (ha : d188486 p = 1) (hb : d192784 p = 1) : d181677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d188486 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45324 q ha hb
    | true =>
      simp only [d16673, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45314 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d188486 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d188486 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d188486 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45314 q ha hb
    | true =>
      simp only [d16676, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45322 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d188486 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d188486 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d188486 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d188486 q = 1) : d181254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45314 q ha hb
    | true =>
      simp only [d16693, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45313 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d188486 q = 1) : d181255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d188486 q = 1) : d181256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d188486 q = 1) : d181257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171139 q = 1) (hb : d188486 q = 1) : d181676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171139, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45319 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45311 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45311 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45321 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9870 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45311 q ha hb
    | true =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45312 q ha hb
  have h21 (q : Pattern) (ha : d9871 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9872 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9873 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d129539 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d188486 q = 1) (hb : d192784 q = 1) : d181677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192784, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d192784, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro45520 (p : Pattern) (ha : d188486 p = 1) (hb : d192790 p = 1) : d181683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192785 q = 1) : d181678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192785, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45519 q ha hb
    | true =>
      simp only [d192785, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192786 q = 1) : d181679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192786, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192786, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d188486 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45315 q ha hb
    | true =>
      simp only [d20638, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d188486 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192787 q = 1) : d181680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192787, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192787, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192788 q = 1) : d181681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192788, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192788, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d188486 q = 1) (hb : d192789 q = 1) : d181682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192789, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192789, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d188486 q = 1) (hb : d192790 q = 1) : d181683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192790, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192790, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45521 (p : Pattern) (ha : d188486 p = 1) (hb : d192796 p = 1) : d181689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192791 q = 1) : d181684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192791, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45520 q ha hb
    | true =>
      simp only [d192791, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45316 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192792 q = 1) : d181685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192792, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192792, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192793 q = 1) : d181686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192793, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192793, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192794 q = 1) : d181687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192794, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192794, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192795 q = 1) : d181688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192795, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192795, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192796 q = 1) : d181689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192796, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192796, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45522 (p : Pattern) (ha : d188486 p = 1) (hb : d192802 p = 1) : d181695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192797 q = 1) : d181690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192797, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192797, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45521 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192798 q = 1) : d181691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192798, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192798, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192799 q = 1) : d181692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192799, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192799, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192800 q = 1) : d181693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192800, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192800, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192801 q = 1) : d181694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192801, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192801, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192802 q = 1) : d181695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192802, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192802, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45523 (p : Pattern) (ha : d188486 p = 1) (hb : d192808 p = 1) : d181701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192803 q = 1) : d181696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192803, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192803, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45522 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192804 q = 1) : d181697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192804, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192804, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192805 q = 1) : d181698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192805, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192805, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192806 q = 1) : d181699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192806, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192806, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192807 q = 1) : d181700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192807, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192807, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192808 q = 1) : d181701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192808, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192808, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45524 (p : Pattern) (ha : d188486 p = 1) (hb : d192812 p = 1) : d181706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d188486 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45350 q ha hb
    | true =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45340 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d188486 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d188486 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d188486 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45340 q ha hb
    | true =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45348 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d188486 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d188486 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d188486 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d188486 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45340 q ha hb
    | true =>
      simp only [d17053, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45339 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d188486 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d188486 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d188486 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171176 q = 1) (hb : d188486 q = 1) : d181705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171176, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45345 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45337 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45337 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45347 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10164 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45337 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45338 q ha hb
  have h21 (q : Pattern) (ha : d10165 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10166 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10167 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d129568 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d188486 q = 1) (hb : d192812 q = 1) : d181706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192812, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d192812, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro45525 (p : Pattern) (ha : d188486 p = 1) (hb : d192818 p = 1) : d181712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192813 q = 1) : d181707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192813, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45524 q ha hb
    | true =>
      simp only [d192813, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192814 q = 1) : d181708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192814, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192814, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d188486 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45341 q ha hb
    | true =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d188486 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192815 q = 1) : d181709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192815, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192815, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192816 q = 1) : d181710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192816, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192816, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d188486 q = 1) (hb : d192817 q = 1) : d181711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192817, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192817, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d188486 q = 1) (hb : d192818 q = 1) : d181712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192818, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192818, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45526 (p : Pattern) (ha : d188486 p = 1) (hb : d192824 p = 1) : d181718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192819 q = 1) : d181713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192819, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45525 q ha hb
    | true =>
      simp only [d192819, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45342 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192820 q = 1) : d181714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192820, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192820, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192821 q = 1) : d181715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192821, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192821, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192822 q = 1) : d181716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192822, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192822, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192823 q = 1) : d181717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192823, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192823, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192824 q = 1) : d181718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192824, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192824, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45527 (p : Pattern) (ha : d188486 p = 1) (hb : d192830 p = 1) : d181724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192825 q = 1) : d181719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192825, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192825, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45526 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192826 q = 1) : d181720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192826, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192826, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192827 q = 1) : d181721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192827, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192827, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192828 q = 1) : d181722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192828, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192828, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192829 q = 1) : d181723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192829, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192829, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192830 q = 1) : d181724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192830, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192830, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45528 (p : Pattern) (ha : d188486 p = 1) (hb : d192836 p = 1) : d181730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192831 q = 1) : d181725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192831, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192831, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45527 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192832 q = 1) : d181726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192832, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192832, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192833 q = 1) : d181727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192833, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192833, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192834 q = 1) : d181728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192834, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192834, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192835 q = 1) : d181729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192835, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192835, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192836 q = 1) : d181730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192836, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192836, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45529 (p : Pattern) (ha : d188486 p = 1) (hb : d192841 p = 1) : d181736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d188486 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45376 q ha hb
    | true =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45366 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d188486 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d188486 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d188486 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45366 q ha hb
    | true =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45374 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d188486 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d188486 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d188486 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d188486 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45366 q ha hb
    | true =>
      simp only [d17417, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45365 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d188486 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d188486 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d188486 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171214 q = 1) (hb : d188486 q = 1) : d181735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171214, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45371 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45363 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45363 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45373 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10441 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45363 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45364 q ha hb
  have h21 (q : Pattern) (ha : d10442 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10443 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10444 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d129598 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d188486 q = 1) (hb : d192841 q = 1) : d181736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192841, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d192841, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro45530 (p : Pattern) (ha : d188486 p = 1) (hb : d192847 p = 1) : d181742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192842 q = 1) : d181737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192842, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45529 q ha hb
    | true =>
      simp only [d192842, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192843 q = 1) : d181738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192843, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192843, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d188486 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45367 q ha hb
    | true =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d188486 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192844 q = 1) : d181739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192844, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192844, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192845 q = 1) : d181740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192845, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192845, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d188486 q = 1) (hb : d192846 q = 1) : d181741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192846, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192846, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d188486 q = 1) (hb : d192847 q = 1) : d181742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192847, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192847, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45531 (p : Pattern) (ha : d188486 p = 1) (hb : d192853 p = 1) : d181748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192848 q = 1) : d181743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192848, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45530 q ha hb
    | true =>
      simp only [d192848, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45368 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192849 q = 1) : d181744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192849, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192849, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192850 q = 1) : d181745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192850, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192850, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192851 q = 1) : d181746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192851, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192851, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192852 q = 1) : d181747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192852, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192852, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192853 q = 1) : d181748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192853, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192853, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45532 (p : Pattern) (ha : d188486 p = 1) (hb : d192859 p = 1) : d181754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192854 q = 1) : d181749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192854, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192854, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45531 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192855 q = 1) : d181750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192855, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192855, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192856 q = 1) : d181751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192856, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192856, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192857 q = 1) : d181752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192857, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192857, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192858 q = 1) : d181753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192858, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192858, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192859 q = 1) : d181754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192859, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192859, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45533 (p : Pattern) (ha : d188486 p = 1) (hb : d192865 p = 1) : d181760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192860 q = 1) : d181755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192860, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192860, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45532 q ha hb
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192861 q = 1) : d181756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192861, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192861, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192862 q = 1) : d181757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192862, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192862, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192863 q = 1) : d181758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192863, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192863, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192864 q = 1) : d181759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192864, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192864, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192865 q = 1) : d181760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192865, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192865, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45534 (p : Pattern) (ha : d188486 p = 1) (hb : d192871 p = 1) : d181766 p = 1 := by
  have h0 (q : Pattern) (ha : d188486 q = 1) (hb : d192763 q = 1) : d181655 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192763, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45512 q ha hb
    | true =>
      simp only [d192763, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45515 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192782 q = 1) : d181674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192782, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192782, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45518 q ha hb
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192783 q = 1) : d181675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192783, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192783, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192809 q = 1) : d181702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192809, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192809, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45523 q ha hb
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192810 q = 1) : d181703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192810, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192810, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192811 q = 1) : d181704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192811, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192811, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d188486 q = 1) (hb : d192837 q = 1) : d181731 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192837, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192837, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45528 q ha hb
  have h8 (q : Pattern) (ha : d188486 q = 1) (hb : d192838 q = 1) : d181732 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192838, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192838, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d188486 q = 1) (hb : d192839 q = 1) : d181733 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192839, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192839, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d188486 q = 1) (hb : d192840 q = 1) : d181734 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192840, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192840, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d188486 q = 1) (hb : d192866 q = 1) : d181761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192866, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192866, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45533 q ha hb
  have h12 (q : Pattern) (ha : d188486 q = 1) (hb : d192867 q = 1) : d181762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192867, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192867, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d188486 q = 1) (hb : d192868 q = 1) : d181763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192868, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192868, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d188486 q = 1) (hb : d192869 q = 1) : d181764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192869, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192869, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d188486 q = 1) (hb : d192870 q = 1) : d181765 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d192870, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d192870, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d188486 q = 1) (hb : d192871 q = 1) : d181766 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d192871, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d192871, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45535 (p : Pattern) (ha : d188486 p = 1) (hb : d192877 p = 1) : d181772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192872 q = 1) : d181767 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d192872, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45534 q ha hb
    | true =>
      simp only [d192872, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192873 q = 1) : d181768 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d192873, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192873, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192874 q = 1) : d181769 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d192874, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192874, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192875 q = 1) : d181770 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d192875, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192875, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192876 q = 1) : d181771 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d192876, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192876, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192877 q = 1) : d181772 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d192877, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192877, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45536 (p : Pattern) (ha : d188486 p = 1) (hb : d192883 p = 1) : d181778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192878 q = 1) : d181773 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d192878, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45535 q ha hb
    | true =>
      simp only [d192878, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192879 q = 1) : d181774 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d192879, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192879, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192880 q = 1) : d181775 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d192880, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192880, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192881 q = 1) : d181776 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d192881, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192881, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192882 q = 1) : d181777 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d192882, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192882, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192883 q = 1) : d181778 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d192883, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192883, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45537 (p : Pattern) (ha : d188486 p = 1) (hb : d192889 p = 1) : d181784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192884 q = 1) : d181779 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45536 q ha hb
    | true =>
      simp only [d192884, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188486 q = 1) (hb : d192885 q = 1) : d181780 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188486 q = 1) (hb : d192886 q = 1) : d181781 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188486 q = 1) (hb : d192887 q = 1) : d181782 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d192887, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192887, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188486 q = 1) (hb : d192888 q = 1) : d181783 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192888, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192888, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188486 q = 1) (hb : d192889 q = 1) : d181784 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192889, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45538 (p : Pattern) (ha : d188487 p = 1) (hb : d192895 p = 1) : d181790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188486 q = 1) (hb : d192890 q = 1) : d181785 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45537 q ha hb
    | true =>
      simp only [d192890, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d188487 q = 1) (hb : d192891 q = 1) : d181786 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d188487, d192891, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188487, d192891, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d188487 q = 1) (hb : d192892 q = 1) : d181787 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192892, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d188487 q = 1) (hb : d192893 q = 1) : d181788 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192893, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d188487 q = 1) (hb : d192894 q = 1) : d181789 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192894, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d188487 q = 1) (hb : d192895 q = 1) : d181790 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192895, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro45539 (p : Pattern) (ha : d188487 p = 1) (hb : d192901 p = 1) : d181796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188487 q = 1) (hb : d192896 q = 1) : d181791 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45538 q ha hb
    | true =>
      simp only [d192896, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188487 q = 1) (hb : d192897 q = 1) : d181792 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188487 q = 1) (hb : d192898 q = 1) : d181793 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188487 q = 1) (hb : d192899 q = 1) : d181794 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188487 q = 1) (hb : d192900 q = 1) : d181795 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188487 q = 1) (hb : d192901 q = 1) : d181796 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45540 (p : Pattern) (ha : d188487 p = 1) (hb : d192907 p = 1) : d181802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188487 q = 1) (hb : d192902 q = 1) : d181797 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45539 q ha hb
    | true =>
      simp only [d192902, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188487 q = 1) (hb : d192903 q = 1) : d181798 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188487 q = 1) (hb : d192904 q = 1) : d181799 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188487 q = 1) (hb : d192905 q = 1) : d181800 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188487 q = 1) (hb : d192906 q = 1) : d181801 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188487 q = 1) (hb : d192907 q = 1) : d181802 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45541 (p : Pattern) (ha : d188487 p = 1) (hb : d192913 p = 1) : d181808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188487 q = 1) (hb : d192908 q = 1) : d181803 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45540 q ha hb
    | true =>
      simp only [d192908, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188487 q = 1) (hb : d192909 q = 1) : d181804 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188487 q = 1) (hb : d192910 q = 1) : d181805 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188487 q = 1) (hb : d192911 q = 1) : d181806 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188487 q = 1) (hb : d192912 q = 1) : d181807 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188487 q = 1) (hb : d192913 q = 1) : d181808 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45542 (p : Pattern) (ha : d181010 p = 1) (hb : d193657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d180925 q = 1) (hb : d193625 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d180925, d193625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45399 q ha hb
    | true =>
      simp only [d180925, d193625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181006 q = 1) (hb : d193653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181006, d193653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181006, d193653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193626 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181007 q = 1) (hb : d193654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181007, d193654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181007, d193654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181008 q = 1) (hb : d193655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181008, d193655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181008, d193655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181009 q = 1) (hb : d193656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181009, d193656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181009, d193656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181010 q = 1) (hb : d193657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181010, d193657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181010, d193657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45543 (p : Pattern) (ha : d181614 p = 1) (hb : d193663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181011 q = 1) (hb : d193658 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181011, d193658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181011, d193658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45542 q ha hb
  have h2 (q : Pattern) (ha : d181610 q = 1) (hb : d193659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181610, d193659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181610, d193659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181611 q = 1) (hb : d193660 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181611, d193660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181611, d193660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181612 q = 1) (hb : d193661 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181612, d193661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181612, d193661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181613 q = 1) (hb : d193662 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181613, d193662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181613, d193662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181614 q = 1) (hb : d193663 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181614, d193663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181614, d193663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45544 (p : Pattern) (ha : d181624 p = 1) (hb : d193691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193680 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d180957 q = 1) (hb : d193652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d180957, d193652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45404 q ha hb
    | true =>
      simp only [d180957, d193652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45399 q ha hb
  have h3 (q : Pattern) (ha : d181620 q = 1) (hb : d193681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181620, d193681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181620, d193681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181621 q = 1) (hb : d193688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181621, d193688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181621, d193688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181622 q = 1) (hb : d193689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181622, d193689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181622, d193689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181623 q = 1) (hb : d193690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181623, d193690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181623, d193690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181624 q = 1) (hb : d193691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181624, d193691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181624, d193691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45545 (p : Pattern) (ha : d181630 p = 1) (hb : d193703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181625 q = 1) (hb : d193692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181625, d193692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181625, d193692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45544 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193698 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181626 q = 1) (hb : d193699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181626, d193699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181626, d193699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181627 q = 1) (hb : d193700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181627, d193700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181627, d193700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181628 q = 1) (hb : d193701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181628, d193701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181628, d193701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181629 q = 1) (hb : d193702 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181629, d193702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181629, d193702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181630 q = 1) (hb : d193703 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181630, d193703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181630, d193703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45546 (p : Pattern) (ha : d181636 p = 1) (hb : d193709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d193640 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181615 q = 1) (hb : d193664 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181615, d193664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181615, d193664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45543 q ha hb
  have h3 (q : Pattern) (ha : d181616 q = 1) (hb : d193665 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181616, d193665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181616, d193665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181617 q = 1) (hb : d193666 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181617, d193666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181617, d193666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181618 q = 1) (hb : d193667 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181618, d193667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181618, d193667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181619 q = 1) (hb : d193668 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181619, d193668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181619, d193668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181631 q = 1) (hb : d193704 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181631, d193704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181631, d193704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45545 q ha hb
  have h8 (q : Pattern) (ha : d181632 q = 1) (hb : d193705 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181632, d193705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181632, d193705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d181633 q = 1) (hb : d193706 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181633, d193706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181633, d193706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181634 q = 1) (hb : d193707 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181634, d193707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181634, d193707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181635 q = 1) (hb : d193708 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181635, d193708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181635, d193708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d181636 q = 1) (hb : d193709 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181636, d193709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181636, d193709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45547 (p : Pattern) (ha : d181642 p = 1) (hb : d193752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181637 q = 1) (hb : d193741 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181637, d193741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45421 q ha hb
    | true =>
      simp only [d181637, d193741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45424 q ha hb
  have h3 (q : Pattern) (ha : d181638 q = 1) (hb : d193742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181638, d193742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181638, d193742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181639 q = 1) (hb : d193749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181639, d193749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181639, d193749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181640 q = 1) (hb : d193750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181640, d193750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181640, d193750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181641 q = 1) (hb : d193751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181641, d193751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181641, d193751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181642 q = 1) (hb : d193752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181642, d193752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181642, d193752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45548 (p : Pattern) (ha : d181648 p = 1) (hb : d193765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181643 q = 1) (hb : d193753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181643, d193753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181643, d193753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45547 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193760 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181644 q = 1) (hb : d193761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181644, d193761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181644, d193761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181645 q = 1) (hb : d193762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181645, d193762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181645, d193762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181646 q = 1) (hb : d193763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181646, d193763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181646, d193763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181647 q = 1) (hb : d193764 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181647, d193764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181647, d193764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181648 q = 1) (hb : d193765 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181648, d193765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181648, d193765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45549 (p : Pattern) (ha : d181654 p = 1) (hb : d193771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181649 q = 1) (hb : d193766 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181649, d193766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181649, d193766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45548 q ha hb
  have h2 (q : Pattern) (ha : d181650 q = 1) (hb : d193767 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181650, d193767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181650, d193767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181651 q = 1) (hb : d193768 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181651, d193768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181651, d193768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181652 q = 1) (hb : d193769 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181652, d193769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181652, d193769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181653 q = 1) (hb : d193770 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181653, d193770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181653, d193770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181654 q = 1) (hb : d193771 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181654, d193771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181654, d193771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45550 (p : Pattern) (ha : d181661 p = 1) (hb : d193820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181656 q = 1) (hb : d193809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181656, d193809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45437 q ha hb
    | true =>
      simp only [d181656, d193809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45440 q ha hb
  have h3 (q : Pattern) (ha : d181657 q = 1) (hb : d193810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181657, d193810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181657, d193810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181658 q = 1) (hb : d193817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181658, d193817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181658, d193817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181659 q = 1) (hb : d193818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181659, d193818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181659, d193818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181660 q = 1) (hb : d193819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181660, d193819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181660, d193819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181661 q = 1) (hb : d193820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181661, d193820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181661, d193820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45551 (p : Pattern) (ha : d181667 p = 1) (hb : d193833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181662 q = 1) (hb : d193821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181662, d193821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181662, d193821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45550 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193828 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181663 q = 1) (hb : d193829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181663, d193829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181663, d193829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181664 q = 1) (hb : d193830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181664, d193830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181664, d193830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181665 q = 1) (hb : d193831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181665, d193831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181665, d193831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181666 q = 1) (hb : d193832 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181666, d193832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181666, d193832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181667 q = 1) (hb : d193833 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181667, d193833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181667, d193833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45552 (p : Pattern) (ha : d181673 p = 1) (hb : d193839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181668 q = 1) (hb : d193834 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181668, d193834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181668, d193834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45551 q ha hb
  have h2 (q : Pattern) (ha : d181669 q = 1) (hb : d193835 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181669, d193835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181669, d193835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181670 q = 1) (hb : d193836 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181670, d193836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181670, d193836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181671 q = 1) (hb : d193837 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181671, d193837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181671, d193837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181672 q = 1) (hb : d193838 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181672, d193838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181672, d193838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181673 q = 1) (hb : d193839 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181673, d193839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181673, d193839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45553 (p : Pattern) (ha : d181677 p = 1) (hb : d193878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181225 q = 1) (hb : d183158 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181225, d183158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45445 q ha hb
    | true =>
      simp only [d181225, d183158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45447 q ha hb
  have h2 (q : Pattern) (ha : d181226 q = 1) (hb : d183159 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181226, d183159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181226, d183159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181227 q = 1) (hb : d183160 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181227, d183160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181227, d183160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181235 q = 1) (hb : d183168 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181235, d183168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45447 q ha hb
    | true =>
      simp only [d181235, d183168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45448 q ha hb
  have h5 (q : Pattern) (ha : d181236 q = 1) (hb : d183169 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181236, d183169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181236, d183169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181237 q = 1) (hb : d183170 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181237, d183170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181237, d183170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181238 q = 1) (hb : d183171 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181238, d183171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181238, d183171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181254 q = 1) (hb : d183187 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181254, d183187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45447 q ha hb
    | true =>
      simp only [d181254, d183187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45452 q ha hb
  have h9 (q : Pattern) (ha : d181255 q = 1) (hb : d183188 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181255, d183188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181255, d183188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181256 q = 1) (hb : d183189 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181256, d183189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181256, d183189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181257 q = 1) (hb : d183190 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181257, d183190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d181257, d183190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d181676 q = 1) (hb : d183200 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181676, d183200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d181676, d183200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d193877 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d181677 q = 1) (hb : d193878 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181677, d193878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d181677, d193878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45554 (p : Pattern) (ha : d181683 p = 1) (hb : d193884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181678 q = 1) (hb : d193879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181678, d193879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45553 q ha hb
    | true =>
      simp only [d181678, d193879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181679 q = 1) (hb : d193880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181679, d193880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181679, d193880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181260 q = 1) (hb : d193870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181260, d193870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45453 q ha hb
    | true =>
      simp only [d181260, d193870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181261 q = 1) (hb : d193871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181261, d193871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181261, d193871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181680 q = 1) (hb : d193881 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181680, d193881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181680, d193881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181681 q = 1) (hb : d193882 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181681, d193882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181681, d193882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181682 q = 1) (hb : d193883 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181682, d193883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181682, d193883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d181683 q = 1) (hb : d193884 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181683, d193884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d181683, d193884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45555 (p : Pattern) (ha : d181689 p = 1) (hb : d193907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181684 q = 1) (hb : d193889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181684, d193889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45554 q ha hb
    | true =>
      simp only [d181684, d193889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45459 q ha hb
  have h3 (q : Pattern) (ha : d181685 q = 1) (hb : d193890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181685, d193890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181685, d193890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181686 q = 1) (hb : d193904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181686, d193904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181686, d193904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181687 q = 1) (hb : d193905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181687, d193905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181687, d193905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181688 q = 1) (hb : d193906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181688, d193906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181688, d193906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181689 q = 1) (hb : d193907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181689, d193907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181689, d193907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45556 (p : Pattern) (ha : d181695 p = 1) (hb : d193920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181690 q = 1) (hb : d193908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181690, d193908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181690, d193908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45555 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193915 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181691 q = 1) (hb : d193916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181691, d193916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181691, d193916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181692 q = 1) (hb : d193917 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181692, d193917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181692, d193917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181693 q = 1) (hb : d193918 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181693, d193918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181693, d193918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181694 q = 1) (hb : d193919 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181694, d193919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181694, d193919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181695 q = 1) (hb : d193920 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181695, d193920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181695, d193920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45557 (p : Pattern) (ha : d181701 p = 1) (hb : d193926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181696 q = 1) (hb : d193921 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181696, d193921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181696, d193921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45556 q ha hb
  have h2 (q : Pattern) (ha : d181697 q = 1) (hb : d193922 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181697, d193922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181697, d193922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181698 q = 1) (hb : d193923 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181698, d193923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181698, d193923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181699 q = 1) (hb : d193924 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181699, d193924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181699, d193924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181700 q = 1) (hb : d193925 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181700, d193925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181700, d193925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181701 q = 1) (hb : d193926 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181701, d193926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181701, d193926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45558 (p : Pattern) (ha : d181706 p = 1) (hb : d193966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181351 q = 1) (hb : d183293 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181351, d183293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45464 q ha hb
    | true =>
      simp only [d181351, d183293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45466 q ha hb
  have h2 (q : Pattern) (ha : d181352 q = 1) (hb : d183294 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181352, d183294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181352, d183294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181353 q = 1) (hb : d183295 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181353, d183295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181353, d183295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181361 q = 1) (hb : d183303 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181361, d183303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45466 q ha hb
    | true =>
      simp only [d181361, d183303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45467 q ha hb
  have h5 (q : Pattern) (ha : d181362 q = 1) (hb : d183304 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181362, d183304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181362, d183304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181363 q = 1) (hb : d183305 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181363, d183305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181363, d183305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181364 q = 1) (hb : d183306 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181364, d183306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181364, d183306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181382 q = 1) (hb : d183324 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181382, d183324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45466 q ha hb
    | true =>
      simp only [d181382, d183324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45471 q ha hb
  have h9 (q : Pattern) (ha : d181383 q = 1) (hb : d183325 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181383, d183325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181383, d183325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181384 q = 1) (hb : d183326 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181384, d183326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181384, d183326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181385 q = 1) (hb : d183327 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181385, d183327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d181385, d183327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d181705 q = 1) (hb : d183337 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181705, d183337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d181705, d183337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d193965 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d181706 q = 1) (hb : d193966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181706, d193966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d181706, d193966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45559 (p : Pattern) (ha : d181712 p = 1) (hb : d193972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181707 q = 1) (hb : d193967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181707, d193967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45558 q ha hb
    | true =>
      simp only [d181707, d193967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181708 q = 1) (hb : d193968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181708, d193968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181708, d193968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181388 q = 1) (hb : d193958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181388, d193958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45472 q ha hb
    | true =>
      simp only [d181388, d193958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181389 q = 1) (hb : d193959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181389, d193959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181389, d193959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181709 q = 1) (hb : d193969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181709, d193969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181709, d193969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181710 q = 1) (hb : d193970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181710, d193970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181710, d193970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181711 q = 1) (hb : d193971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181711, d193971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181711, d193971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d181712 q = 1) (hb : d193972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181712, d193972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d181712, d193972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45560 (p : Pattern) (ha : d181718 p = 1) (hb : d193995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193964 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181713 q = 1) (hb : d193977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181713, d193977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45559 q ha hb
    | true =>
      simp only [d181713, d193977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45478 q ha hb
  have h3 (q : Pattern) (ha : d181714 q = 1) (hb : d193978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181714, d193978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181714, d193978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193991 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181715 q = 1) (hb : d193992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181715, d193992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181715, d193992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181716 q = 1) (hb : d193993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181716, d193993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181716, d193993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181717 q = 1) (hb : d193994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181717, d193994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181717, d193994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181718 q = 1) (hb : d193995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181718, d193995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181718, d193995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45561 (p : Pattern) (ha : d181724 p = 1) (hb : d194008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181719 q = 1) (hb : d193996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181719, d193996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181719, d193996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45560 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194003 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181720 q = 1) (hb : d194004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181720, d194004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181720, d194004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181721 q = 1) (hb : d194005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181721, d194005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181721, d194005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181722 q = 1) (hb : d194006 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181722, d194006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181722, d194006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181723 q = 1) (hb : d194007 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181723, d194007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181723, d194007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181724 q = 1) (hb : d194008 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181724, d194008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181724, d194008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45562 (p : Pattern) (ha : d181730 p = 1) (hb : d194014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181725 q = 1) (hb : d194009 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181725, d194009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181725, d194009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45561 q ha hb
  have h2 (q : Pattern) (ha : d181726 q = 1) (hb : d194010 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181726, d194010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181726, d194010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181727 q = 1) (hb : d194011 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181727, d194011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181727, d194011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181728 q = 1) (hb : d194012 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181728, d194012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181728, d194012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181729 q = 1) (hb : d194013 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181729, d194013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181729, d194013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181730 q = 1) (hb : d194014 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181730, d194014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181730, d194014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45563 (p : Pattern) (ha : d181736 p = 1) (hb : d194055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181475 q = 1) (hb : d183426 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181475, d183426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45483 q ha hb
    | true =>
      simp only [d181475, d183426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45485 q ha hb
  have h2 (q : Pattern) (ha : d181476 q = 1) (hb : d183427 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181476, d183427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181476, d183427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181477 q = 1) (hb : d183428 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181477, d183428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181477, d183428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181485 q = 1) (hb : d183436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181485, d183436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45485 q ha hb
    | true =>
      simp only [d181485, d183436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45486 q ha hb
  have h5 (q : Pattern) (ha : d181486 q = 1) (hb : d183437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181486, d183437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181486, d183437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181487 q = 1) (hb : d183438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181487, d183438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181487, d183438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181488 q = 1) (hb : d183439 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181488, d183439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181488, d183439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181506 q = 1) (hb : d183457 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181506, d183457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45485 q ha hb
    | true =>
      simp only [d181506, d183457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45490 q ha hb
  have h9 (q : Pattern) (ha : d181507 q = 1) (hb : d183458 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181507, d183458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181507, d183458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181508 q = 1) (hb : d183459 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181508, d183459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181508, d183459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181509 q = 1) (hb : d183460 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181509, d183460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d181509, d183460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d181735 q = 1) (hb : d183470 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181735, d183470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d181735, d183470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d194054 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d181736 q = 1) (hb : d194055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181736, d194055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d181736, d194055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45564 (p : Pattern) (ha : d181742 p = 1) (hb : d194061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181737 q = 1) (hb : d194056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181737, d194056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45563 q ha hb
    | true =>
      simp only [d181737, d194056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181738 q = 1) (hb : d194057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181738, d194057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181738, d194057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181512 q = 1) (hb : d194047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181512, d194047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45491 q ha hb
    | true =>
      simp only [d181512, d194047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181513 q = 1) (hb : d194048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181513, d194048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181513, d194048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181739 q = 1) (hb : d194058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181739, d194058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181739, d194058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181740 q = 1) (hb : d194059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181740, d194059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181740, d194059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181741 q = 1) (hb : d194060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181741, d194060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181741, d194060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d181742 q = 1) (hb : d194061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181742, d194061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d181742, d194061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45565 (p : Pattern) (ha : d181748 p = 1) (hb : d194084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d194053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181743 q = 1) (hb : d194066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181743, d194066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45564 q ha hb
    | true =>
      simp only [d181743, d194066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45497 q ha hb
  have h3 (q : Pattern) (ha : d181744 q = 1) (hb : d194067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181744, d194067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181744, d194067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d194080 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181745 q = 1) (hb : d194081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181745, d194081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181745, d194081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181746 q = 1) (hb : d194082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181746, d194082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181746, d194082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181747 q = 1) (hb : d194083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181747, d194083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181747, d194083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181748 q = 1) (hb : d194084 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181748, d194084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181748, d194084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45566 (p : Pattern) (ha : d181754 p = 1) (hb : d194097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181749 q = 1) (hb : d194085 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181749, d194085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181749, d194085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45565 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181750 q = 1) (hb : d194093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181750, d194093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181750, d194093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181751 q = 1) (hb : d194094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181751, d194094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181751, d194094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181752 q = 1) (hb : d194095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181752, d194095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181752, d194095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181753 q = 1) (hb : d194096 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181753, d194096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181753, d194096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181754 q = 1) (hb : d194097 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181754, d194097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181754, d194097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45567 (p : Pattern) (ha : d181760 p = 1) (hb : d194103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181755 q = 1) (hb : d194098 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181755, d194098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181755, d194098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45566 q ha hb
  have h2 (q : Pattern) (ha : d181756 q = 1) (hb : d194099 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181756, d194099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181756, d194099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181757 q = 1) (hb : d194100 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181757, d194100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181757, d194100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181758 q = 1) (hb : d194101 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181758, d194101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181758, d194101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181759 q = 1) (hb : d194102 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181759, d194102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181759, d194102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181760 q = 1) (hb : d194103 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181760, d194103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181760, d194103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45568 (p : Pattern) (ha : d181766 p = 1) (hb : d194109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d181655 q = 1) (hb : d193772 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181655, d193772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45546 q ha hb
    | true =>
      simp only [d181655, d193772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45549 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181674 q = 1) (hb : d193840 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181674, d193840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181674, d193840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45552 q ha hb
  have h3 (q : Pattern) (ha : d181675 q = 1) (hb : d193841 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181675, d193841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181675, d193841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181702 q = 1) (hb : d193927 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181702, d193927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181702, d193927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45557 q ha hb
  have h5 (q : Pattern) (ha : d181703 q = 1) (hb : d193928 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181703, d193928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181703, d193928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181704 q = 1) (hb : d193929 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181704, d193929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181704, d193929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181731 q = 1) (hb : d194015 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181731, d194015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181731, d194015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45562 q ha hb
  have h8 (q : Pattern) (ha : d181732 q = 1) (hb : d194016 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181732, d194016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181732, d194016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d181733 q = 1) (hb : d194017 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181733, d194017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181733, d194017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181734 q = 1) (hb : d194018 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d181734, d194018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181734, d194018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181761 q = 1) (hb : d194104 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181761, d194104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181761, d194104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45567 q ha hb
  have h12 (q : Pattern) (ha : d181762 q = 1) (hb : d194105 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181762, d194105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181762, d194105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d181763 q = 1) (hb : d194106 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181763, d194106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181763, d194106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d181764 q = 1) (hb : d194107 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d181764, d194107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181764, d194107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d181765 q = 1) (hb : d194108 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d181765, d194108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d181765, d194108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d181766 q = 1) (hb : d194109 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d181766, d194109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d181766, d194109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro45569 (p : Pattern) (ha : d181772 p = 1) (hb : d194115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181767 q = 1) (hb : d194110 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d181767, d194110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45568 q ha hb
    | true =>
      simp only [d181767, d194110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181768 q = 1) (hb : d194111 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d181768, d194111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181768, d194111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181769 q = 1) (hb : d194112 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d181769, d194112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181769, d194112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181770 q = 1) (hb : d194113 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d181770, d194113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181770, d194113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181771 q = 1) (hb : d194114 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d181771, d194114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181771, d194114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181772 q = 1) (hb : d194115 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d181772, d194115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181772, d194115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45570 (p : Pattern) (ha : d181778 p = 1) (hb : d194121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181773 q = 1) (hb : d194116 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d181773, d194116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45569 q ha hb
    | true =>
      simp only [d181773, d194116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181774 q = 1) (hb : d194117 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d181774, d194117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181774, d194117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181775 q = 1) (hb : d194118 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d181775, d194118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181775, d194118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181776 q = 1) (hb : d194119 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d181776, d194119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181776, d194119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181777 q = 1) (hb : d194120 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d181777, d194120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181777, d194120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181778 q = 1) (hb : d194121 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d181778, d194121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181778, d194121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45571 (p : Pattern) (ha : d181784 p = 1) (hb : d194127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181779 q = 1) (hb : d194122 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d181779, d194122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45570 q ha hb
    | true =>
      simp only [d181779, d194122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181780 q = 1) (hb : d194123 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d181780, d194123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181780, d194123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181781 q = 1) (hb : d194124 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d181781, d194124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181781, d194124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181782 q = 1) (hb : d194125 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d181782, d194125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181782, d194125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181783 q = 1) (hb : d194126 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d181783, d194126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181783, d194126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181784 q = 1) (hb : d194127 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d181784, d194127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181784, d194127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45572 (p : Pattern) (ha : d181790 p = 1) (hb : d194133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181785 q = 1) (hb : d194128 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d181785, d194128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45571 q ha hb
    | true =>
      simp only [d181785, d194128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181786 q = 1) (hb : d194129 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d181786, d194129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181786, d194129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181787 q = 1) (hb : d194130 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d181787, d194130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181787, d194130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181788 q = 1) (hb : d194131 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d181788, d194131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181788, d194131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181789 q = 1) (hb : d194132 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d181789, d194132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181789, d194132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181790 q = 1) (hb : d194133 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d181790, d194133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181790, d194133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45573 (p : Pattern) (ha : d181796 p = 1) (hb : d194139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181791 q = 1) (hb : d194134 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d181791, d194134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45572 q ha hb
    | true =>
      simp only [d181791, d194134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181792 q = 1) (hb : d194135 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d181792, d194135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181792, d194135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181793 q = 1) (hb : d194136 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d181793, d194136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181793, d194136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181794 q = 1) (hb : d194137 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d181794, d194137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181794, d194137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181795 q = 1) (hb : d194138 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d181795, d194138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181795, d194138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181796 q = 1) (hb : d194139 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d181796, d194139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181796, d194139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45574 (p : Pattern) (ha : d181802 p = 1) (hb : d194145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181797 q = 1) (hb : d194140 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d181797, d194140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45573 q ha hb
    | true =>
      simp only [d181797, d194140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181798 q = 1) (hb : d194141 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d181798, d194141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181798, d194141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181799 q = 1) (hb : d194142 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d181799, d194142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181799, d194142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181800 q = 1) (hb : d194143 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d181800, d194143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181800, d194143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181801 q = 1) (hb : d194144 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d181801, d194144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181801, d194144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181802 q = 1) (hb : d194145 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d181802, d194145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181802, d194145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45575 (p : Pattern) (ha : d181808 p = 1) (hb : d194151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181803 q = 1) (hb : d194146 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d181803, d194146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45574 q ha hb
    | true =>
      simp only [d181803, d194146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181804 q = 1) (hb : d194147 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d181804, d194147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181804, d194147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181805 q = 1) (hb : d194148 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d181805, d194148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181805, d194148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181806 q = 1) (hb : d194149 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d181806, d194149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181806, d194149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181807 q = 1) (hb : d194150 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d181807, d194150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181807, d194150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181808 q = 1) (hb : d194151 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d181808, d194151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181808, d194151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45576 (p : Pattern) (ha : d181010 p = 1) (hb : d194156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193000 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181006 q = 1) (hb : d194152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181006, d194152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181006, d194152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d192974 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181007 q = 1) (hb : d194153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181007, d194153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181007, d194153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181008 q = 1) (hb : d194154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181008, d194154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181008, d194154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181009 q = 1) (hb : d194155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181009, d194155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181009, d194155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181010 q = 1) (hb : d194156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181010, d194156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181010, d194156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45577 (p : Pattern) (ha : d181614 p = 1) (hb : d194162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181011 q = 1) (hb : d194157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181011, d194157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181011, d194157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45576 q ha hb
  have h2 (q : Pattern) (ha : d181610 q = 1) (hb : d194158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181610, d194158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181610, d194158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181611 q = 1) (hb : d194159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181611, d194159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181611, d194159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181612 q = 1) (hb : d194160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181612, d194160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181612, d194160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181613 q = 1) (hb : d194161 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181613, d194161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181613, d194161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181614 q = 1) (hb : d194162 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181614, d194162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181614, d194162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45578 (p : Pattern) (ha : d181624 p = 1) (hb : d194172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181620 q = 1) (hb : d194168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181620, d194168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181620, d194168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193059 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181621 q = 1) (hb : d194169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181621, d194169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181621, d194169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181622 q = 1) (hb : d194170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181622, d194170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181622, d194170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181623 q = 1) (hb : d194171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181623, d194171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181623, d194171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181624 q = 1) (hb : d194172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181624, d194172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181624, d194172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45579 (p : Pattern) (ha : d181630 p = 1) (hb : d194178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181625 q = 1) (hb : d194173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181625, d194173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181625, d194173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45578 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181626 q = 1) (hb : d194174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181626, d194174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181626, d194174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181627 q = 1) (hb : d194175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181627, d194175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181627, d194175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181628 q = 1) (hb : d194176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181628, d194176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181628, d194176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181629 q = 1) (hb : d194177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181629, d194177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181629, d194177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181630 q = 1) (hb : d194178 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181630, d194178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181630, d194178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45580 (p : Pattern) (ha : d181636 p = 1) (hb : d194184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181615 q = 1) (hb : d194163 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181615, d194163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181615, d194163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45577 q ha hb
  have h3 (q : Pattern) (ha : d181616 q = 1) (hb : d194164 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181616, d194164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181616, d194164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181617 q = 1) (hb : d194165 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181617, d194165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181617, d194165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181618 q = 1) (hb : d194166 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181618, d194166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181618, d194166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181619 q = 1) (hb : d194167 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181619, d194167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181619, d194167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181631 q = 1) (hb : d194179 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181631, d194179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181631, d194179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45579 q ha hb
  have h8 (q : Pattern) (ha : d181632 q = 1) (hb : d194180 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181632, d194180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181632, d194180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d181633 q = 1) (hb : d194181 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181633, d194181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181633, d194181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181634 q = 1) (hb : d194182 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181634, d194182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181634, d194182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181635 q = 1) (hb : d194183 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181635, d194183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181635, d194183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d181636 q = 1) (hb : d194184 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181636, d194184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181636, d194184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45581 (p : Pattern) (ha : d181642 p = 1) (hb : d194189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181638 q = 1) (hb : d194185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181638, d194185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181638, d194185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193136 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181639 q = 1) (hb : d194186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181639, d194186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181639, d194186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181640 q = 1) (hb : d194187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181640, d194187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181640, d194187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181641 q = 1) (hb : d194188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181641, d194188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181641, d194188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181642 q = 1) (hb : d194189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181642, d194189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181642, d194189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45582 (p : Pattern) (ha : d181648 p = 1) (hb : d194195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181643 q = 1) (hb : d194190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181643, d194190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181643, d194190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45581 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181644 q = 1) (hb : d194191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181644, d194191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181644, d194191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181645 q = 1) (hb : d194192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181645, d194192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181645, d194192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181646 q = 1) (hb : d194193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181646, d194193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181646, d194193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181647 q = 1) (hb : d194194 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181647, d194194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181647, d194194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181648 q = 1) (hb : d194195 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181648, d194195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181648, d194195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45583 (p : Pattern) (ha : d181654 p = 1) (hb : d194201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181649 q = 1) (hb : d194196 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181649, d194196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181649, d194196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45582 q ha hb
  have h2 (q : Pattern) (ha : d181650 q = 1) (hb : d194197 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181650, d194197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181650, d194197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181651 q = 1) (hb : d194198 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181651, d194198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181651, d194198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181652 q = 1) (hb : d194199 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181652, d194199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181652, d194199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181653 q = 1) (hb : d194200 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181653, d194200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181653, d194200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181654 q = 1) (hb : d194201 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181654, d194201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181654, d194201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45584 (p : Pattern) (ha : d181661 p = 1) (hb : d194207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193196 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181656 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181657 q = 1) (hb : d194203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181657, d194203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181657, d194203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193226 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181658 q = 1) (hb : d194204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181658, d194204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181658, d194204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181659 q = 1) (hb : d194205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181659, d194205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181659, d194205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181660 q = 1) (hb : d194206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181660, d194206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181660, d194206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181661 q = 1) (hb : d194207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181661, d194207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181661, d194207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45585 (p : Pattern) (ha : d181667 p = 1) (hb : d194213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181662 q = 1) (hb : d194208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181662, d194208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181662, d194208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45584 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193242 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181663 q = 1) (hb : d194209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181663, d194209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181663, d194209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181664 q = 1) (hb : d194210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181664, d194210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181664, d194210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181665 q = 1) (hb : d194211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181665, d194211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181665, d194211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181666 q = 1) (hb : d194212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181666, d194212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181666, d194212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181667 q = 1) (hb : d194213 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181667, d194213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181667, d194213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45586 (p : Pattern) (ha : d181673 p = 1) (hb : d194219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181668 q = 1) (hb : d194214 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181668, d194214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181668, d194214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45585 q ha hb
  have h2 (q : Pattern) (ha : d181669 q = 1) (hb : d194215 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181669, d194215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181669, d194215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181670 q = 1) (hb : d194216 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181670, d194216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181670, d194216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181671 q = 1) (hb : d194217 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181671, d194217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181671, d194217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181672 q = 1) (hb : d194218 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181672, d194218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181672, d194218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181673 q = 1) (hb : d194219 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181673, d194219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181673, d194219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45587 (p : Pattern) (ha : d181689 p = 1) (hb : d194226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193290 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181684 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181685 q = 1) (hb : d194222 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181685, d194222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181685, d194222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193329 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181686 q = 1) (hb : d194223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181686, d194223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181686, d194223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181687 q = 1) (hb : d194224 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181687, d194224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181687, d194224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181688 q = 1) (hb : d194225 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181688, d194225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181688, d194225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181689 q = 1) (hb : d194226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181689, d194226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181689, d194226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45588 (p : Pattern) (ha : d181695 p = 1) (hb : d194232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181690 q = 1) (hb : d194227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181690, d194227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181690, d194227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45587 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193345 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181691 q = 1) (hb : d194228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181691, d194228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181691, d194228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181692 q = 1) (hb : d194229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181692, d194229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181692, d194229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181693 q = 1) (hb : d194230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181693, d194230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181693, d194230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181694 q = 1) (hb : d194231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181694, d194231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181694, d194231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181695 q = 1) (hb : d194232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181695, d194232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181695, d194232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45589 (p : Pattern) (ha : d181701 p = 1) (hb : d194238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181696 q = 1) (hb : d194233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181696, d194233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181696, d194233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45588 q ha hb
  have h2 (q : Pattern) (ha : d181697 q = 1) (hb : d194234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181697, d194234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181697, d194234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181698 q = 1) (hb : d194235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181698, d194235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181698, d194235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181699 q = 1) (hb : d194236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181699, d194236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181699, d194236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181700 q = 1) (hb : d194237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181700, d194237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181700, d194237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181701 q = 1) (hb : d194238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181701, d194238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181701, d194238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45590 (p : Pattern) (ha : d181718 p = 1) (hb : d194246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181714 q = 1) (hb : d194242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181714, d194242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181714, d194242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193433 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181715 q = 1) (hb : d194243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181715, d194243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181715, d194243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181716 q = 1) (hb : d194244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181716, d194244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181716, d194244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181717 q = 1) (hb : d194245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181717, d194245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181717, d194245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181718 q = 1) (hb : d194246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181718, d194246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181718, d194246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45591 (p : Pattern) (ha : d181724 p = 1) (hb : d194252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181719 q = 1) (hb : d194247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181719, d194247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181719, d194247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45590 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193449 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181720 q = 1) (hb : d194248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181720, d194248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181720, d194248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181721 q = 1) (hb : d194249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181721, d194249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181721, d194249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181722 q = 1) (hb : d194250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181722, d194250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181722, d194250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181723 q = 1) (hb : d194251 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181723, d194251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181723, d194251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181724 q = 1) (hb : d194252 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181724, d194252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181724, d194252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45592 (p : Pattern) (ha : d181730 p = 1) (hb : d194258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181725 q = 1) (hb : d194253 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181725, d194253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181725, d194253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45591 q ha hb
  have h2 (q : Pattern) (ha : d181726 q = 1) (hb : d194254 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181726, d194254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181726, d194254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181727 q = 1) (hb : d194255 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181727, d194255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181727, d194255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181728 q = 1) (hb : d194256 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181728, d194256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181728, d194256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181729 q = 1) (hb : d194257 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181729, d194257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181729, d194257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181730 q = 1) (hb : d194258 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181730, d194258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181730, d194258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45593 (p : Pattern) (ha : d181748 p = 1) (hb : d194267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d193499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181744 q = 1) (hb : d194263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181744, d194263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181744, d194263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d193538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d181745 q = 1) (hb : d194264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181745, d194264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181745, d194264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181746 q = 1) (hb : d194265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181746, d194265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181746, d194265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181747 q = 1) (hb : d194266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181747, d194266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181747, d194266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d181748 q = 1) (hb : d194267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181748, d194267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181748, d194267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45594 (p : Pattern) (ha : d181754 p = 1) (hb : d194273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181749 q = 1) (hb : d194268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181749, d194268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181749, d194268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45593 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d193554 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d181750 q = 1) (hb : d194269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181750, d194269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181750, d194269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181751 q = 1) (hb : d194270 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181751, d194270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181751, d194270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181752 q = 1) (hb : d194271 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181752, d194271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181752, d194271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181753 q = 1) (hb : d194272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181753, d194272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181753, d194272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d181754 q = 1) (hb : d194273 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181754, d194273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181754, d194273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45595 (p : Pattern) (ha : d181760 p = 1) (hb : d194279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181755 q = 1) (hb : d194274 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181755, d194274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181755, d194274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45594 q ha hb
  have h2 (q : Pattern) (ha : d181756 q = 1) (hb : d194275 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181756, d194275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181756, d194275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d181757 q = 1) (hb : d194276 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181757, d194276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181757, d194276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181758 q = 1) (hb : d194277 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181758, d194277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181758, d194277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d181759 q = 1) (hb : d194278 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181759, d194278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181759, d194278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181760 q = 1) (hb : d194279 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d181760, d194279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181760, d194279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45596 (p : Pattern) (ha : d181766 p = 1) (hb : d194285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d181655 q = 1) (hb : d194202 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181655, d194202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45580 q ha hb
    | true =>
      simp only [d181655, d194202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45583 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d181674 q = 1) (hb : d194220 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181674, d194220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181674, d194220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45586 q ha hb
  have h3 (q : Pattern) (ha : d181675 q = 1) (hb : d194221 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181675, d194221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d181675, d194221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d181702 q = 1) (hb : d194239 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181702, d194239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181702, d194239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45589 q ha hb
  have h5 (q : Pattern) (ha : d181703 q = 1) (hb : d194240 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181703, d194240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181703, d194240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d181704 q = 1) (hb : d194241 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181704, d194241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181704, d194241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d181731 q = 1) (hb : d194259 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181731, d194259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181731, d194259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45592 q ha hb
  have h8 (q : Pattern) (ha : d181732 q = 1) (hb : d194260 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181732, d194260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181732, d194260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d181733 q = 1) (hb : d194261 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181733, d194261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181733, d194261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d181734 q = 1) (hb : d194262 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d181734, d194262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d181734, d194262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d181761 q = 1) (hb : d194280 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d181761, d194280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181761, d194280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45595 q ha hb
  have h12 (q : Pattern) (ha : d181762 q = 1) (hb : d194281 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d181762, d194281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181762, d194281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d181763 q = 1) (hb : d194282 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d181763, d194282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181763, d194282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d181764 q = 1) (hb : d194283 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d181764, d194283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181764, d194283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d181765 q = 1) (hb : d194284 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d181765, d194284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d181765, d194284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d181766 q = 1) (hb : d194285 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d181766, d194285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d181766, d194285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro45597 (p : Pattern) (ha : d181772 p = 1) (hb : d194291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181767 q = 1) (hb : d194286 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d181767, d194286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45596 q ha hb
    | true =>
      simp only [d181767, d194286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181768 q = 1) (hb : d194287 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d181768, d194287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181768, d194287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181769 q = 1) (hb : d194288 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d181769, d194288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181769, d194288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181770 q = 1) (hb : d194289 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d181770, d194289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181770, d194289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181771 q = 1) (hb : d194290 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d181771, d194290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181771, d194290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181772 q = 1) (hb : d194291 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d181772, d194291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181772, d194291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45598 (p : Pattern) (ha : d181778 p = 1) (hb : d194297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181773 q = 1) (hb : d194292 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d181773, d194292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45597 q ha hb
    | true =>
      simp only [d181773, d194292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181774 q = 1) (hb : d194293 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d181774, d194293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181774, d194293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181775 q = 1) (hb : d194294 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d181775, d194294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181775, d194294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181776 q = 1) (hb : d194295 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d181776, d194295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181776, d194295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181777 q = 1) (hb : d194296 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d181777, d194296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181777, d194296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181778 q = 1) (hb : d194297 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d181778, d194297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181778, d194297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45599 (p : Pattern) (ha : d181784 p = 1) (hb : d194303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181779 q = 1) (hb : d194298 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d181779, d194298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45598 q ha hb
    | true =>
      simp only [d181779, d194298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181780 q = 1) (hb : d194299 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d181780, d194299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181780, d194299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181781 q = 1) (hb : d194300 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d181781, d194300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181781, d194300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181782 q = 1) (hb : d194301 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d181782, d194301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181782, d194301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181783 q = 1) (hb : d194302 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d181783, d194302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181783, d194302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181784 q = 1) (hb : d194303 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d181784, d194303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181784, d194303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45600 (p : Pattern) (ha : d181790 p = 1) (hb : d194309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181785 q = 1) (hb : d194304 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d181785, d194304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45599 q ha hb
    | true =>
      simp only [d181785, d194304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181786 q = 1) (hb : d194305 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d181786, d194305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181786, d194305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181787 q = 1) (hb : d194306 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d181787, d194306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181787, d194306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181788 q = 1) (hb : d194307 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d181788, d194307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181788, d194307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181789 q = 1) (hb : d194308 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d181789, d194308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181789, d194308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181790 q = 1) (hb : d194309 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d181790, d194309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181790, d194309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45601 (p : Pattern) (ha : d181796 p = 1) (hb : d194315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181791 q = 1) (hb : d194310 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d181791, d194310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45600 q ha hb
    | true =>
      simp only [d181791, d194310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181792 q = 1) (hb : d194311 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d181792, d194311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181792, d194311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181793 q = 1) (hb : d194312 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d181793, d194312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181793, d194312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181794 q = 1) (hb : d194313 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d181794, d194313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181794, d194313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181795 q = 1) (hb : d194314 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d181795, d194314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181795, d194314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181796 q = 1) (hb : d194315 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d181796, d194315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181796, d194315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45602 (p : Pattern) (ha : d181802 p = 1) (hb : d194321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181797 q = 1) (hb : d194316 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d181797, d194316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45601 q ha hb
    | true =>
      simp only [d181797, d194316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181798 q = 1) (hb : d194317 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d181798, d194317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181798, d194317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181799 q = 1) (hb : d194318 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d181799, d194318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181799, d194318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181800 q = 1) (hb : d194319 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d181800, d194319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181800, d194319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181801 q = 1) (hb : d194320 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d181801, d194320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181801, d194320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181802 q = 1) (hb : d194321 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d181802, d194321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181802, d194321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45603 (p : Pattern) (ha : d181808 p = 1) (hb : d194327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181803 q = 1) (hb : d194322 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d181803, d194322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45602 q ha hb
    | true =>
      simp only [d181803, d194322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d181804 q = 1) (hb : d194323 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d181804, d194323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d181804, d194323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d181805 q = 1) (hb : d194324 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d181805, d194324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d181805, d194324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d181806 q = 1) (hb : d194325 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d181806, d194325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d181806, d194325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d181807 q = 1) (hb : d194326 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d181807, d194326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d181807, d194326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d181808 q = 1) (hb : d194327 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d181808, d194327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d181808, d194327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45604 (p : Pattern) (ha : d20390 p = 1) (hb : d129672 p = 1) : d9302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d72 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d73 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9301 q = 1) (hb : d129672 q = 1) : d9301 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20390 q = 1) (hb : d129672 q = 1) : d9302 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20390, d9302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20390, d9302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45605 (p : Pattern) (ha : d20396 p = 1) (hb : d129672 p = 1) : d9308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20391 q = 1) (hb : d129672 q = 1) : d9303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45604 q ha hb
    | true =>
      simp only [d20391, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20392 q = 1) (hb : d129672 q = 1) : d9304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20393 q = 1) (hb : d129672 q = 1) : d9305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20393, d9305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20393, d9305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20394 q = 1) (hb : d129672 q = 1) : d9306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20394, d9306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20394, d9306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20395 q = 1) (hb : d129672 q = 1) : d9307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20395, d9307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20395, d9307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20396 q = 1) (hb : d129672 q = 1) : d9308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20396, d9308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20396, d9308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45606 (p : Pattern) (ha : d20402 p = 1) (hb : d129672 p = 1) : d9314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d129672 q = 1) : d9309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45605 q ha hb
    | true =>
      simp only [d20397, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20398 q = 1) (hb : d129672 q = 1) : d9310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20398, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20399 q = 1) (hb : d129672 q = 1) : d9311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20399, d9311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20399, d9311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20400 q = 1) (hb : d129672 q = 1) : d9312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20400, d9312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20400, d9312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20401 q = 1) (hb : d129672 q = 1) : d9313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20401, d9313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20401, d9313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20402 q = 1) (hb : d129672 q = 1) : d9314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20402, d9314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20402, d9314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45607 (p : Pattern) (ha : d20408 p = 1) (hb : d129672 p = 1) : d9320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20403 q = 1) (hb : d129672 q = 1) : d9315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20403, d9315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20403, d9315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45606 q ha hb
  have h2 (q : Pattern) (ha : d20404 q = 1) (hb : d129672 q = 1) : d9316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20404, d9316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20404, d9316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20405 q = 1) (hb : d129672 q = 1) : d9317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20405, d9317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20405, d9317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20406 q = 1) (hb : d129672 q = 1) : d9318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20406, d9318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20406, d9318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20407 q = 1) (hb : d129672 q = 1) : d9319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20407, d9319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20407, d9319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20408 q = 1) (hb : d129672 q = 1) : d9320 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20408, d9320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20408, d9320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45608 (p : Pattern) (ha : d20413 p = 1) (hb : d129672 p = 1) : d9335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d72 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d236 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9334 q = 1) (hb : d129672 q = 1) : d9334 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20413 q = 1) (hb : d129672 q = 1) : d9335 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20413, d9335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20413, d9335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45609 (p : Pattern) (ha : d20419 p = 1) (hb : d129672 p = 1) : d9341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d129672 q = 1) : d9336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45608 q ha hb
    | true =>
      simp only [d20414, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d129672 q = 1) : d9337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20391 q = 1) (hb : d129672 q = 1) : d9303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45604 q ha hb
    | true =>
      simp only [d20391, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20392 q = 1) (hb : d129672 q = 1) : d9304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20416 q = 1) (hb : d129672 q = 1) : d9338 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20416, d9338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20416, d9338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20417 q = 1) (hb : d129672 q = 1) : d9339 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20417, d9339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20417, d9339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20418 q = 1) (hb : d129672 q = 1) : d9340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20418, d9340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20418, d9340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20419 q = 1) (hb : d129672 q = 1) : d9341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20419, d9341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20419, d9341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45610 (p : Pattern) (ha : d129672 p = 1) (hb : d130924 p = 1) : d101879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d129672 q = 1) : d9342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45609 q ha hb
    | true =>
      simp only [d20420, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45605 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130920 q = 1) : d101875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130920, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130920, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20397 q = 1) (hb : d129672 q = 1) : d9309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45605 q ha hb
    | true =>
      simp only [d20397, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20398 q = 1) (hb : d129672 q = 1) : d9310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20398, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130921 q = 1) : d101876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130921, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130921, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130922 q = 1) : d101877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130922, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130922, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130923 q = 1) : d101878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130923, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130923, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130924 q = 1) : d101879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130924, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130924, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45611 (p : Pattern) (ha : d129672 p = 1) (hb : d130930 p = 1) : d101885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130925 q = 1) : d101880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130925, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130925, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45610 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130926 q = 1) : d101881 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130926, d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130926, d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130927 q = 1) : d101882 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130927, d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130927, d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130928 q = 1) : d101883 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130928, d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130928, d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130929 q = 1) : d101884 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130929, d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130929, d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130930 q = 1) : d101885 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130930, d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130930, d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45612 (p : Pattern) (ha : d20477 p = 1) (hb : d129672 p = 1) : d9436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d129672 q = 1) : d9309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45605 q ha hb
    | true =>
      simp only [d20397, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20473 q = 1) (hb : d129672 q = 1) : d9432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, d9432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20473, d9432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20474 q = 1) (hb : d129672 q = 1) : d9433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, d9433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20474, d9433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20475 q = 1) (hb : d129672 q = 1) : d9434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, d9434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20475, d9434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20476 q = 1) (hb : d129672 q = 1) : d9435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, d9435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20476, d9435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20477 q = 1) (hb : d129672 q = 1) : d9436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, d9436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20477, d9436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45613 (p : Pattern) (ha : d20445 p = 1) (hb : d129672 p = 1) : d9394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16006 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16006, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16007 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d72 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d73 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d235 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16009 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9393 q = 1) (hb : d129672 q = 1) : d9393 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20445 q = 1) (hb : d129672 q = 1) : d9394 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20445, d9394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20445, d9394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45614 (p : Pattern) (ha : d20451 p = 1) (hb : d129672 p = 1) : d9400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20446 q = 1) (hb : d129672 q = 1) : d9395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20446, d9395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45613 q ha hb
    | true =>
      simp only [d20446, d9395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20447 q = 1) (hb : d129672 q = 1) : d9396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20447, d9396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20447, d9396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20414 q = 1) (hb : d129672 q = 1) : d9336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45608 q ha hb
    | true =>
      simp only [d20414, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20415 q = 1) (hb : d129672 q = 1) : d9337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20448 q = 1) (hb : d129672 q = 1) : d9397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20448, d9397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20448, d9397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20449 q = 1) (hb : d129672 q = 1) : d9398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20449, d9398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20449, d9398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20450 q = 1) (hb : d129672 q = 1) : d9399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20450, d9399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20450, d9399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20451 q = 1) (hb : d129672 q = 1) : d9400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20451, d9400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20451, d9400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45615 (p : Pattern) (ha : d20465 p = 1) (hb : d129672 p = 1) : d9424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d129672 q = 1) : d9336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45608 q ha hb
    | true =>
      simp only [d20414, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d129672 q = 1) : d9337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20462 q = 1) (hb : d129672 q = 1) : d9421 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20462, d9421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20462, d9421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20463 q = 1) (hb : d129672 q = 1) : d9422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20463, d9422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20463, d9422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20464 q = 1) (hb : d129672 q = 1) : d9423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20464, d9423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20464, d9423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20465 q = 1) (hb : d129672 q = 1) : d9424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20465, d9424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20465, d9424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45616 (p : Pattern) (ha : d129672 p = 1) (hb : d130940 p = 1) : d101895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20452 q = 1) (hb : d129672 q = 1) : d9401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20452, d9401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45614 q ha hb
    | true =>
      simp only [d20452, d9401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45609 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130936 q = 1) : d101891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130936, d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130936, d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20466 q = 1) (hb : d129672 q = 1) : d9425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20466, d9425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45615 q ha hb
    | true =>
      simp only [d20466, d9425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20467 q = 1) (hb : d129672 q = 1) : d9426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20467, d9426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20467, d9426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130937 q = 1) : d101892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130937, d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130937, d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130938 q = 1) : d101893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130938, d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130938, d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130939 q = 1) : d101894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130939, d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130939, d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130940 q = 1) : d101895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130940, d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130940, d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45617 (p : Pattern) (ha : d129672 p = 1) (hb : d130946 p = 1) : d101901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130941 q = 1) : d101896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130941, d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130941, d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45616 q ha hb
  have h2 (q : Pattern) (ha : d20478 q = 1) (hb : d129672 q = 1) : d9437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45612 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130942 q = 1) : d101897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130942, d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130942, d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130943 q = 1) : d101898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130943, d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130943, d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130944 q = 1) : d101899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130944, d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130944, d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130945 q = 1) : d101900 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130945, d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130945, d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130946 q = 1) : d101901 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130946, d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130946, d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45618 (p : Pattern) (ha : d129672 p = 1) (hb : d130952 p = 1) : d101907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20409 q = 1) (hb : d129672 q = 1) : d9321 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20409, d9321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20409, d9321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45607 q ha hb
  have h2 (q : Pattern) (ha : d20410 q = 1) (hb : d129672 q = 1) : d9322 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20410, d9322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20410, d9322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20411 q = 1) (hb : d129672 q = 1) : d9323 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20411, d9323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20411, d9323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20412 q = 1) (hb : d129672 q = 1) : d9324 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20412, d9324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20412, d9324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130931 q = 1) : d101886 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130931, d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130931, d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45611 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130932 q = 1) : d101887 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130932, d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130932, d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130933 q = 1) : d101888 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130933, d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130933, d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130934 q = 1) : d101889 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130934, d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130934, d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d130935 q = 1) : d101890 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130935, d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d130935, d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d130947 q = 1) : d101902 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130947, d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130947, d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45617 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d130948 q = 1) : d101903 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130948, d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130948, d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129672 q = 1) (hb : d130949 q = 1) : d101904 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130949, d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130949, d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d130950 q = 1) : d101905 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130950, d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130950, d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129672 q = 1) (hb : d130951 q = 1) : d101906 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130951, d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130951, d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d130952 q = 1) : d101907 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130952, d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130952, d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45619 (p : Pattern) (ha : d20500 p = 1) (hb : d129672 p = 1) : d9497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9496 q = 1) (hb : d129672 q = 1) : d9496 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20500 q = 1) (hb : d129672 q = 1) : d9497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20500, d9497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20500, d9497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45620 (p : Pattern) (ha : d20538 p = 1) (hb : d129672 p = 1) : d9556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20501 q = 1) (hb : d129672 q = 1) : d9498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45619 q ha hb
    | true =>
      simp only [d20501, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20502 q = 1) (hb : d129672 q = 1) : d9499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20535 q = 1) (hb : d129672 q = 1) : d9553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20535, d9553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20535, d9553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20536 q = 1) (hb : d129672 q = 1) : d9554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20536, d9554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20536, d9554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20537 q = 1) (hb : d129672 q = 1) : d9555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20537, d9555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20537, d9555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20538 q = 1) (hb : d129672 q = 1) : d9556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20538, d9556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20538, d9556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45621 (p : Pattern) (ha : d20544 p = 1) (hb : d129672 p = 1) : d9562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20539 q = 1) (hb : d129672 q = 1) : d9557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20539, d9557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45620 q ha hb
    | true =>
      simp only [d20539, d9557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20540 q = 1) (hb : d129672 q = 1) : d9558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20540, d9558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20540, d9558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20541 q = 1) (hb : d129672 q = 1) : d9559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20541, d9559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20541, d9559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20542 q = 1) (hb : d129672 q = 1) : d9560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20542, d9560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20542, d9560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20543 q = 1) (hb : d129672 q = 1) : d9561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20543, d9561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20543, d9561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20544 q = 1) (hb : d129672 q = 1) : d9562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20544, d9562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20544, d9562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45622 (p : Pattern) (ha : d20490 p = 1) (hb : d129672 p = 1) : d9484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16164 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16164, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16165 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16167 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16168 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16168, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16169 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16170 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16005 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16006 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16006, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16007 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9483 q = 1) (hb : d129672 q = 1) : d9483 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20490 q = 1) (hb : d129672 q = 1) : d9484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20490, d9484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20490, d9484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45623 (p : Pattern) (ha : d20493 p = 1) (hb : d129672 p = 1) : d9489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16006 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16006, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16007 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9488 q = 1) (hb : d129672 q = 1) : d9488 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20493 q = 1) (hb : d129672 q = 1) : d9489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20493, d9489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20493, d9489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45624 (p : Pattern) (ha : d20499 p = 1) (hb : d129672 p = 1) : d9495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20491 q = 1) (hb : d129672 q = 1) : d9485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20491, d9485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45622 q ha hb
    | true =>
      simp only [d20491, d9485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20492 q = 1) (hb : d129672 q = 1) : d9486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20492, d9486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20492, d9486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20494 q = 1) (hb : d129672 q = 1) : d9490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45623 q ha hb
    | true =>
      simp only [d20494, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20495 q = 1) (hb : d129672 q = 1) : d9491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20496 q = 1) (hb : d129672 q = 1) : d9492 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20496, d9492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20496, d9492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20497 q = 1) (hb : d129672 q = 1) : d9493 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20497, d9493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20497, d9493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20498 q = 1) (hb : d129672 q = 1) : d9494 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20498, d9494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20498, d9494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20499 q = 1) (hb : d129672 q = 1) : d9495 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20499, d9495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20499, d9495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45625 (p : Pattern) (ha : d20506 p = 1) (hb : d129672 p = 1) : d9503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d129672 q = 1) : d9490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45623 q ha hb
    | true =>
      simp only [d20494, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d129672 q = 1) : d9491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20501 q = 1) (hb : d129672 q = 1) : d9498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45619 q ha hb
    | true =>
      simp only [d20501, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20502 q = 1) (hb : d129672 q = 1) : d9499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20503 q = 1) (hb : d129672 q = 1) : d9500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20503, d9500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20503, d9500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20504 q = 1) (hb : d129672 q = 1) : d9501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20504, d9501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20504, d9501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20505 q = 1) (hb : d129672 q = 1) : d9502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20505, d9502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20505, d9502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20506 q = 1) (hb : d129672 q = 1) : d9503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20506, d9503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20506, d9503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45626 (p : Pattern) (ha : d20527 p = 1) (hb : d129672 p = 1) : d9545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d129672 q = 1) : d9490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45623 q ha hb
    | true =>
      simp only [d20494, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d129672 q = 1) : d9491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20524 q = 1) (hb : d129672 q = 1) : d9542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20524, d9542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20524, d9542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20525 q = 1) (hb : d129672 q = 1) : d9543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20525, d9543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20525, d9543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20526 q = 1) (hb : d129672 q = 1) : d9544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20526, d9544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20526, d9544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20527 q = 1) (hb : d129672 q = 1) : d9545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20527, d9545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20527, d9545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45627 (p : Pattern) (ha : d129672 p = 1) (hb : d130957 p = 1) : d101912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20507 q = 1) (hb : d129672 q = 1) : d9504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20507, d9504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45624 q ha hb
    | true =>
      simp only [d20507, d9504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45625 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130953 q = 1) : d101908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130953, d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130953, d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20528 q = 1) (hb : d129672 q = 1) : d9546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20528, d9546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45626 q ha hb
    | true =>
      simp only [d20528, d9546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20529 q = 1) (hb : d129672 q = 1) : d9547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20529, d9547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20529, d9547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130954 q = 1) : d101909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130954, d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130954, d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130955 q = 1) : d101910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130955, d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130955, d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130956 q = 1) : d101911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130956, d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130956, d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130957 q = 1) : d101912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130957, d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130957, d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45628 (p : Pattern) (ha : d129672 p = 1) (hb : d130963 p = 1) : d101918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130958 q = 1) : d101913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130958, d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130958, d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45627 q ha hb
  have h2 (q : Pattern) (ha : d20545 q = 1) (hb : d129672 q = 1) : d9563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20545, d9563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20545, d9563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45621 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130959 q = 1) : d101914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130959, d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130959, d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130960 q = 1) : d101915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130960, d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130960, d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130961 q = 1) : d101916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130961, d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130961, d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130962 q = 1) : d101917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130962, d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130962, d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130963 q = 1) : d101918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130963, d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130963, d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45629 (p : Pattern) (ha : d129672 p = 1) (hb : d130969 p = 1) : d101924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130964 q = 1) : d101919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130964, d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130964, d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45628 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130965 q = 1) : d101920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130965, d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130965, d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130966 q = 1) : d101921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130966, d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130966, d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130967 q = 1) : d101922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130967, d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130967, d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130968 q = 1) : d101923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130968, d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130968, d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130969 q = 1) : d101924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130969, d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130969, d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45630 (p : Pattern) (ha : d20568 p = 1) (hb : d129672 p = 1) : d9642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d987 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9641 q = 1) (hb : d129672 q = 1) : d9641 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20568 q = 1) (hb : d129672 q = 1) : d9642 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20568, d9642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20568, d9642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45631 (p : Pattern) (ha : d20606 p = 1) (hb : d129672 p = 1) : d9725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20569 q = 1) (hb : d129672 q = 1) : d9643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45630 q ha hb
    | true =>
      simp only [d20569, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20570 q = 1) (hb : d129672 q = 1) : d9644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20603 q = 1) (hb : d129672 q = 1) : d9722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20603, d9722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20603, d9722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20604 q = 1) (hb : d129672 q = 1) : d9723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20604, d9723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20604, d9723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20605 q = 1) (hb : d129672 q = 1) : d9724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20605, d9724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20605, d9724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20606 q = 1) (hb : d129672 q = 1) : d9725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20606, d9725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20606, d9725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45632 (p : Pattern) (ha : d20612 p = 1) (hb : d129672 p = 1) : d9731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20607 q = 1) (hb : d129672 q = 1) : d9726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20607, d9726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45631 q ha hb
    | true =>
      simp only [d20607, d9726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20608 q = 1) (hb : d129672 q = 1) : d9727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20608, d9727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20608, d9727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20609 q = 1) (hb : d129672 q = 1) : d9728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20609, d9728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20609, d9728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20610 q = 1) (hb : d129672 q = 1) : d9729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20610, d9729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20610, d9729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20611 q = 1) (hb : d129672 q = 1) : d9730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20611, d9730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20611, d9730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20612 q = 1) (hb : d129672 q = 1) : d9731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20612, d9731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20612, d9731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45633 (p : Pattern) (ha : d20558 p = 1) (hb : d129672 p = 1) : d9629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16365 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16365, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16366 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16368 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16369 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16369, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16370 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16371 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16372 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16373 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16373, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16374 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d987 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16375 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16376 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9628 q = 1) (hb : d129672 q = 1) : d9628 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20558 q = 1) (hb : d129672 q = 1) : d9629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20558, d9629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20558, d9629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45634 (p : Pattern) (ha : d20561 p = 1) (hb : d129672 p = 1) : d9634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16372 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16373 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16373, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16374 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d987 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16375 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16380 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9633 q = 1) (hb : d129672 q = 1) : d9633 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20561 q = 1) (hb : d129672 q = 1) : d9634 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20561, d9634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20561, d9634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45635 (p : Pattern) (ha : d20567 p = 1) (hb : d129672 p = 1) : d9640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20559 q = 1) (hb : d129672 q = 1) : d9630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20559, d9630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45633 q ha hb
    | true =>
      simp only [d20559, d9630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20560 q = 1) (hb : d129672 q = 1) : d9631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20560, d9631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20560, d9631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20562 q = 1) (hb : d129672 q = 1) : d9635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45634 q ha hb
    | true =>
      simp only [d20562, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20563 q = 1) (hb : d129672 q = 1) : d9636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20564 q = 1) (hb : d129672 q = 1) : d9637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20564, d9637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20564, d9637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20565 q = 1) (hb : d129672 q = 1) : d9638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20565, d9638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20565, d9638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20566 q = 1) (hb : d129672 q = 1) : d9639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20566, d9639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20566, d9639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20567 q = 1) (hb : d129672 q = 1) : d9640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20567, d9640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20567, d9640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45636 (p : Pattern) (ha : d20574 p = 1) (hb : d129672 p = 1) : d9648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d129672 q = 1) : d9635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45634 q ha hb
    | true =>
      simp only [d20562, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d129672 q = 1) : d9636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20569 q = 1) (hb : d129672 q = 1) : d9643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45630 q ha hb
    | true =>
      simp only [d20569, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20570 q = 1) (hb : d129672 q = 1) : d9644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20571 q = 1) (hb : d129672 q = 1) : d9645 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20571, d9645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20571, d9645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20572 q = 1) (hb : d129672 q = 1) : d9646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20572, d9646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20572, d9646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20573 q = 1) (hb : d129672 q = 1) : d9647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20573, d9647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20573, d9647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20574 q = 1) (hb : d129672 q = 1) : d9648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20574, d9648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20574, d9648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45637 (p : Pattern) (ha : d20595 p = 1) (hb : d129672 p = 1) : d9714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d129672 q = 1) : d9635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45634 q ha hb
    | true =>
      simp only [d20562, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d129672 q = 1) : d9636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20592 q = 1) (hb : d129672 q = 1) : d9711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20592, d9711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20592, d9711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20593 q = 1) (hb : d129672 q = 1) : d9712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20593, d9712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20593, d9712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20594 q = 1) (hb : d129672 q = 1) : d9713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20594, d9713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20594, d9713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20595 q = 1) (hb : d129672 q = 1) : d9714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20595, d9714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20595, d9714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45638 (p : Pattern) (ha : d129672 p = 1) (hb : d130975 p = 1) : d101930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20575 q = 1) (hb : d129672 q = 1) : d9649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20575, d9649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45635 q ha hb
    | true =>
      simp only [d20575, d9649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45636 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130971 q = 1) : d101926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130971, d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130971, d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20596 q = 1) (hb : d129672 q = 1) : d9715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20596, d9715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45637 q ha hb
    | true =>
      simp only [d20596, d9715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20597 q = 1) (hb : d129672 q = 1) : d9716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20597, d9716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20597, d9716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130972 q = 1) : d101927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130972, d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130972, d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130973 q = 1) : d101928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130973, d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130973, d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130974 q = 1) : d101929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130974, d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130974, d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130975 q = 1) : d101930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130975, d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130975, d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45639 (p : Pattern) (ha : d129672 p = 1) (hb : d130981 p = 1) : d101936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130976 q = 1) : d101931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130976, d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130976, d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45638 q ha hb
  have h2 (q : Pattern) (ha : d20613 q = 1) (hb : d129672 q = 1) : d9732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20613, d9732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20613, d9732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45632 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130977 q = 1) : d101932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130977, d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130977, d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130978 q = 1) : d101933 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130978, d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130978, d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130979 q = 1) : d101934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130979, d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130979, d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130980 q = 1) : d101935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130980, d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130980, d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130981 q = 1) : d101936 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130981, d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130981, d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45640 (p : Pattern) (ha : d129672 p = 1) (hb : d130987 p = 1) : d101942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130982 q = 1) : d101937 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130982, d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130982, d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45639 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130983 q = 1) : d101938 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130983, d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130983, d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130984 q = 1) : d101939 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130984, d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130984, d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130985 q = 1) : d101940 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130985, d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130985, d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130986 q = 1) : d101941 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130986, d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130986, d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130987 q = 1) : d101942 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130987, d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130987, d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45641 (p : Pattern) (ha : d20637 p = 1) (hb : d129672 p = 1) : d9875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16693 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16694 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16694, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16695 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16696 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16697 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9874 q = 1) (hb : d129672 q = 1) : d9874 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20637 q = 1) (hb : d129672 q = 1) : d9875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20637, d9875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20637, d9875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45642 (p : Pattern) (ha : d20678 p = 1) (hb : d129672 p = 1) : d10010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20638 q = 1) (hb : d129672 q = 1) : d9876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45641 q ha hb
    | true =>
      simp only [d20638, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20639 q = 1) (hb : d129672 q = 1) : d9877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20675 q = 1) (hb : d129672 q = 1) : d10007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20675, d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20675, d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20676 q = 1) (hb : d129672 q = 1) : d10008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20676, d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20676, d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20677 q = 1) (hb : d129672 q = 1) : d10009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20677, d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20677, d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20678 q = 1) (hb : d129672 q = 1) : d10010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20678, d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20678, d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45643 (p : Pattern) (ha : d20684 p = 1) (hb : d129672 p = 1) : d10016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20679 q = 1) (hb : d129672 q = 1) : d10011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20679, d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45642 q ha hb
    | true =>
      simp only [d20679, d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20680 q = 1) (hb : d129672 q = 1) : d10012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20680, d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20680, d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20681 q = 1) (hb : d129672 q = 1) : d10013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20681, d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20681, d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20682 q = 1) (hb : d129672 q = 1) : d10014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20682, d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20682, d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20683 q = 1) (hb : d129672 q = 1) : d10015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20683, d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20683, d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20684 q = 1) (hb : d129672 q = 1) : d10016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20684, d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20684, d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45644 (p : Pattern) (ha : d20627 p = 1) (hb : d129672 p = 1) : d9856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16663 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16664 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16664, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16665 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16668 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16669 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16669, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16670 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16671 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16674 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16675 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d16677 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d16678 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16679 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16680 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9855 q = 1) (hb : d129672 q = 1) : d9855 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20627 q = 1) (hb : d129672 q = 1) : d9856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20627, d9856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20627, d9856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45645 (p : Pattern) (ha : d20630 p = 1) (hb : d129672 p = 1) : d9861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16674 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16675 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16684 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16685 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9860 q = 1) (hb : d129672 q = 1) : d9860 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20630 q = 1) (hb : d129672 q = 1) : d9861 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20630, d9861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20630, d9861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45646 (p : Pattern) (ha : d20636 p = 1) (hb : d129672 p = 1) : d9867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20628 q = 1) (hb : d129672 q = 1) : d9857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20628, d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45644 q ha hb
    | true =>
      simp only [d20628, d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20629 q = 1) (hb : d129672 q = 1) : d9858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20629, d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20629, d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20631 q = 1) (hb : d129672 q = 1) : d9862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45645 q ha hb
    | true =>
      simp only [d20631, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20632 q = 1) (hb : d129672 q = 1) : d9863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20633 q = 1) (hb : d129672 q = 1) : d9864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20633, d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20633, d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20634 q = 1) (hb : d129672 q = 1) : d9865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20634, d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20634, d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20635 q = 1) (hb : d129672 q = 1) : d9866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20635, d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20635, d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20636 q = 1) (hb : d129672 q = 1) : d9867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20636, d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20636, d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45647 (p : Pattern) (ha : d20643 p = 1) (hb : d129672 p = 1) : d9881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20631 q = 1) (hb : d129672 q = 1) : d9862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45645 q ha hb
    | true =>
      simp only [d20631, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20632 q = 1) (hb : d129672 q = 1) : d9863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d129672 q = 1) : d9876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45641 q ha hb
    | true =>
      simp only [d20638, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d129672 q = 1) : d9877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20640 q = 1) (hb : d129672 q = 1) : d9878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20640, d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20640, d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20641 q = 1) (hb : d129672 q = 1) : d9879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20641, d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20641, d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20642 q = 1) (hb : d129672 q = 1) : d9880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20642, d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20642, d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20643 q = 1) (hb : d129672 q = 1) : d9881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20643, d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20643, d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45648 (p : Pattern) (ha : d20661 p = 1) (hb : d129672 p = 1) : d9993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16674 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16675 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16743 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16744 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16744, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16745 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16746 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16747 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9992 q = 1) (hb : d129672 q = 1) : d9992 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20661 q = 1) (hb : d129672 q = 1) : d9993 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20661, d9993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20661, d9993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45649 (p : Pattern) (ha : d20667 p = 1) (hb : d129672 p = 1) : d9999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20662 q = 1) (hb : d129672 q = 1) : d9994 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20662, d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45648 q ha hb
    | true =>
      simp only [d20662, d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20663 q = 1) (hb : d129672 q = 1) : d9995 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20663, d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20663, d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20664 q = 1) (hb : d129672 q = 1) : d9996 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20664, d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20664, d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20665 q = 1) (hb : d129672 q = 1) : d9997 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20665, d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20665, d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20666 q = 1) (hb : d129672 q = 1) : d9998 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20666, d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20666, d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20667 q = 1) (hb : d129672 q = 1) : d9999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20667, d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20667, d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45650 (p : Pattern) (ha : d129672 p = 1) (hb : d130994 p = 1) : d101949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20644 q = 1) (hb : d129672 q = 1) : d9882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20644, d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45646 q ha hb
    | true =>
      simp only [d20644, d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45647 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130990 q = 1) : d101945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130990, d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20668 q = 1) (hb : d129672 q = 1) : d10000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20668, d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45649 q ha hb
    | true =>
      simp only [d20668, d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20669 q = 1) (hb : d129672 q = 1) : d10001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20669, d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20669, d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130991 q = 1) : d101946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130991, d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130992 q = 1) : d101947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130992, d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130993 q = 1) : d101948 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130993, d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130994 q = 1) : d101949 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130994, d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45651 (p : Pattern) (ha : d129672 p = 1) (hb : d131000 p = 1) : d101955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130995 q = 1) : d101950 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130995, d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45650 q ha hb
  have h2 (q : Pattern) (ha : d20685 q = 1) (hb : d129672 q = 1) : d10017 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20685, d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20685, d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45643 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130996 q = 1) : d101951 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130997 q = 1) : d101952 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130998 q = 1) : d101953 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130999 q = 1) : d101954 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d131000 q = 1) : d101955 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131000, d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45652 (p : Pattern) (ha : d129672 p = 1) (hb : d131006 p = 1) : d101961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131001 q = 1) : d101956 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131001, d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45651 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131002 q = 1) : d101957 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131002, d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131003 q = 1) : d101958 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131003, d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131004 q = 1) : d101959 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131004, d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131005 q = 1) : d101960 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131005, d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131006 q = 1) : d101961 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131006, d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45653 (p : Pattern) (ha : d20710 p = 1) (hb : d129672 p = 1) : d10169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17054 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17054, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17055 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17056 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17057 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10168 q = 1) (hb : d129672 q = 1) : d10168 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20710 q = 1) (hb : d129672 q = 1) : d10169 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20710, d10169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20710, d10169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45654 (p : Pattern) (ha : d20751 p = 1) (hb : d129672 p = 1) : d10316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20711 q = 1) (hb : d129672 q = 1) : d10170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45653 q ha hb
    | true =>
      simp only [d20711, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20712 q = 1) (hb : d129672 q = 1) : d10171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20748 q = 1) (hb : d129672 q = 1) : d10313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20748, d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20748, d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20749 q = 1) (hb : d129672 q = 1) : d10314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20749, d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20749, d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20750 q = 1) (hb : d129672 q = 1) : d10315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20750, d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20750, d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20751 q = 1) (hb : d129672 q = 1) : d10316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20751, d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20751, d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45655 (p : Pattern) (ha : d20757 p = 1) (hb : d129672 p = 1) : d10322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20752 q = 1) (hb : d129672 q = 1) : d10317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20752, d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45654 q ha hb
    | true =>
      simp only [d20752, d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20753 q = 1) (hb : d129672 q = 1) : d10318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20753, d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20753, d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20754 q = 1) (hb : d129672 q = 1) : d10319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20754, d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20754, d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20755 q = 1) (hb : d129672 q = 1) : d10320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20755, d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20755, d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20756 q = 1) (hb : d129672 q = 1) : d10321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20756, d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20756, d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20757 q = 1) (hb : d129672 q = 1) : d10322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20757, d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20757, d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45656 (p : Pattern) (ha : d20700 p = 1) (hb : d129672 p = 1) : d10147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17019 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17019, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17020 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17024 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17024, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17025 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17026 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17034 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17035 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d17038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17040 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10146 q = 1) (hb : d129672 q = 1) : d10146 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20700 q = 1) (hb : d129672 q = 1) : d10147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20700, d10147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20700, d10147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45657 (p : Pattern) (ha : d20703 p = 1) (hb : d129672 p = 1) : d10152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17034 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17035 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17044 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17045 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10151 q = 1) (hb : d129672 q = 1) : d10151 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20703 q = 1) (hb : d129672 q = 1) : d10152 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20703, d10152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20703, d10152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45658 (p : Pattern) (ha : d20709 p = 1) (hb : d129672 p = 1) : d10158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20701 q = 1) (hb : d129672 q = 1) : d10148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20701, d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45656 q ha hb
    | true =>
      simp only [d20701, d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20702 q = 1) (hb : d129672 q = 1) : d10149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20702, d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20702, d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20704 q = 1) (hb : d129672 q = 1) : d10153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45657 q ha hb
    | true =>
      simp only [d20704, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20705 q = 1) (hb : d129672 q = 1) : d10154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20706 q = 1) (hb : d129672 q = 1) : d10155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20706, d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20706, d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20707 q = 1) (hb : d129672 q = 1) : d10156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20707, d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20707, d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20708 q = 1) (hb : d129672 q = 1) : d10157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20708, d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20708, d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20709 q = 1) (hb : d129672 q = 1) : d10158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20709, d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20709, d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45659 (p : Pattern) (ha : d20716 p = 1) (hb : d129672 p = 1) : d10175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20704 q = 1) (hb : d129672 q = 1) : d10153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45657 q ha hb
    | true =>
      simp only [d20704, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20705 q = 1) (hb : d129672 q = 1) : d10154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d129672 q = 1) : d10170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45653 q ha hb
    | true =>
      simp only [d20711, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d129672 q = 1) : d10171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20713 q = 1) (hb : d129672 q = 1) : d10172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20713, d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20713, d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20714 q = 1) (hb : d129672 q = 1) : d10173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20714, d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20714, d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20715 q = 1) (hb : d129672 q = 1) : d10174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20715, d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20715, d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20716 q = 1) (hb : d129672 q = 1) : d10175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20716, d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20716, d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45660 (p : Pattern) (ha : d20734 p = 1) (hb : d129672 p = 1) : d10299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17034 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17035 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17108 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17109 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17109, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17110 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17111 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17112 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10298 q = 1) (hb : d129672 q = 1) : d10298 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20734 q = 1) (hb : d129672 q = 1) : d10299 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20734, d10299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20734, d10299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45661 (p : Pattern) (ha : d20740 p = 1) (hb : d129672 p = 1) : d10305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20735 q = 1) (hb : d129672 q = 1) : d10300 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20735, d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45660 q ha hb
    | true =>
      simp only [d20735, d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20736 q = 1) (hb : d129672 q = 1) : d10301 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20736, d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20736, d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20737 q = 1) (hb : d129672 q = 1) : d10302 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20737, d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20737, d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20738 q = 1) (hb : d129672 q = 1) : d10303 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20738, d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20738, d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20739 q = 1) (hb : d129672 q = 1) : d10304 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20739, d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20739, d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20740 q = 1) (hb : d129672 q = 1) : d10305 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20740, d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20740, d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45662 (p : Pattern) (ha : d129672 p = 1) (hb : d131014 p = 1) : d101969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20717 q = 1) (hb : d129672 q = 1) : d10176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20717, d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45658 q ha hb
    | true =>
      simp only [d20717, d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45659 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131010 q = 1) : d101965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131010, d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20741 q = 1) (hb : d129672 q = 1) : d10306 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20741, d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45661 q ha hb
    | true =>
      simp only [d20741, d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20742 q = 1) (hb : d129672 q = 1) : d10307 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20742, d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20742, d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131011 q = 1) : d101966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131011, d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131012 q = 1) : d101967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131012, d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d131013 q = 1) : d101968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131013, d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d131014 q = 1) : d101969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131014, d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45663 (p : Pattern) (ha : d129672 p = 1) (hb : d131020 p = 1) : d101975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131015 q = 1) : d101970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131015, d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45662 q ha hb
  have h2 (q : Pattern) (ha : d20758 q = 1) (hb : d129672 q = 1) : d10323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20758, d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20758, d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45655 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131016 q = 1) : d101971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131017 q = 1) : d101972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131018 q = 1) : d101973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131019 q = 1) : d101974 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d131020 q = 1) : d101975 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131020, d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45664 (p : Pattern) (ha : d129672 p = 1) (hb : d131026 p = 1) : d101981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131021 q = 1) : d101976 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131021, d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45663 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131022 q = 1) : d101977 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131022, d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131023 q = 1) : d101978 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131023, d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131024 q = 1) : d101979 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131024, d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131025 q = 1) : d101980 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131025, d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131026 q = 1) : d101981 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131026, d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45665 (p : Pattern) (ha : d20784 p = 1) (hb : d129672 p = 1) : d10446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17418 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17418, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17419 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17420 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17421 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10445 q = 1) (hb : d129672 q = 1) : d10445 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20784 q = 1) (hb : d129672 q = 1) : d10446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20784, d10446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20784, d10446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45666 (p : Pattern) (ha : d20825 p = 1) (hb : d129672 p = 1) : d10582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20785 q = 1) (hb : d129672 q = 1) : d10447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45665 q ha hb
    | true =>
      simp only [d20785, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20786 q = 1) (hb : d129672 q = 1) : d10448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20822 q = 1) (hb : d129672 q = 1) : d10579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20822, d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20822, d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20823 q = 1) (hb : d129672 q = 1) : d10580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20823, d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20823, d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20824 q = 1) (hb : d129672 q = 1) : d10581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20824, d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20824, d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20825 q = 1) (hb : d129672 q = 1) : d10582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20825, d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20825, d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45667 (p : Pattern) (ha : d20831 p = 1) (hb : d129672 p = 1) : d10588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20826 q = 1) (hb : d129672 q = 1) : d10583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20826, d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45666 q ha hb
    | true =>
      simp only [d20826, d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20827 q = 1) (hb : d129672 q = 1) : d10584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20827, d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20827, d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20828 q = 1) (hb : d129672 q = 1) : d10585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20828, d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20828, d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20829 q = 1) (hb : d129672 q = 1) : d10586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20829, d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20829, d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20830 q = 1) (hb : d129672 q = 1) : d10587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20830, d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20830, d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20831 q = 1) (hb : d129672 q = 1) : d10588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20831, d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20831, d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45668 (p : Pattern) (ha : d20774 p = 1) (hb : d129672 p = 1) : d10424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17384 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17384, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17385 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17387 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17388 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17388, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17389 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17390 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17398 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17399 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17401 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d17402 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17403 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17404 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10423 q = 1) (hb : d129672 q = 1) : d10423 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20774 q = 1) (hb : d129672 q = 1) : d10424 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20774, d10424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20774, d10424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45669 (p : Pattern) (ha : d20777 p = 1) (hb : d129672 p = 1) : d10429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17398 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17399 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17408 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17409 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10428 q = 1) (hb : d129672 q = 1) : d10428 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20777 q = 1) (hb : d129672 q = 1) : d10429 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20777, d10429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20777, d10429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45670 (p : Pattern) (ha : d20783 p = 1) (hb : d129672 p = 1) : d10435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20775 q = 1) (hb : d129672 q = 1) : d10425 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20775, d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45668 q ha hb
    | true =>
      simp only [d20775, d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20776 q = 1) (hb : d129672 q = 1) : d10426 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20776, d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20776, d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20778 q = 1) (hb : d129672 q = 1) : d10430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45669 q ha hb
    | true =>
      simp only [d20778, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20779 q = 1) (hb : d129672 q = 1) : d10431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20780 q = 1) (hb : d129672 q = 1) : d10432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20780, d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20780, d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20781 q = 1) (hb : d129672 q = 1) : d10433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20781, d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20781, d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20782 q = 1) (hb : d129672 q = 1) : d10434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20782, d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20782, d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20783 q = 1) (hb : d129672 q = 1) : d10435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20783, d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20783, d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45671 (p : Pattern) (ha : d20790 p = 1) (hb : d129672 p = 1) : d10452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20778 q = 1) (hb : d129672 q = 1) : d10430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45669 q ha hb
    | true =>
      simp only [d20778, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20779 q = 1) (hb : d129672 q = 1) : d10431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d129672 q = 1) : d10447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45665 q ha hb
    | true =>
      simp only [d20785, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d129672 q = 1) : d10448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20787 q = 1) (hb : d129672 q = 1) : d10449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20787, d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20787, d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20788 q = 1) (hb : d129672 q = 1) : d10450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20788, d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20788, d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20789 q = 1) (hb : d129672 q = 1) : d10451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20789, d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20789, d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20790 q = 1) (hb : d129672 q = 1) : d10452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20790, d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20790, d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45672 (p : Pattern) (ha : d20808 p = 1) (hb : d129672 p = 1) : d10565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17398 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17399 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17472 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17473 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17473, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17474 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17475 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17476 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10564 q = 1) (hb : d129672 q = 1) : d10564 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20808 q = 1) (hb : d129672 q = 1) : d10565 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20808, d10565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20808, d10565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45673 (p : Pattern) (ha : d20814 p = 1) (hb : d129672 p = 1) : d10571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20809 q = 1) (hb : d129672 q = 1) : d10566 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20809, d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45672 q ha hb
    | true =>
      simp only [d20809, d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20810 q = 1) (hb : d129672 q = 1) : d10567 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20810, d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20810, d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20811 q = 1) (hb : d129672 q = 1) : d10568 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20811, d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20811, d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20812 q = 1) (hb : d129672 q = 1) : d10569 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20812, d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20812, d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20813 q = 1) (hb : d129672 q = 1) : d10570 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20813, d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20813, d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20814 q = 1) (hb : d129672 q = 1) : d10571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20814, d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20814, d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45674 (p : Pattern) (ha : d129672 p = 1) (hb : d131035 p = 1) : d101990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20791 q = 1) (hb : d129672 q = 1) : d10453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20791, d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45670 q ha hb
    | true =>
      simp only [d20791, d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45671 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131031 q = 1) : d101986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131031, d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20815 q = 1) (hb : d129672 q = 1) : d10572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20815, d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45673 q ha hb
    | true =>
      simp only [d20815, d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20816 q = 1) (hb : d129672 q = 1) : d10573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20816, d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20816, d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131032 q = 1) : d101987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131032, d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131033 q = 1) : d101988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131033, d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d131034 q = 1) : d101989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131034, d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d131035 q = 1) : d101990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131035, d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45675 (p : Pattern) (ha : d129672 p = 1) (hb : d131041 p = 1) : d101996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131036 q = 1) : d101991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131036, d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45674 q ha hb
  have h2 (q : Pattern) (ha : d20832 q = 1) (hb : d129672 q = 1) : d10589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20832, d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20832, d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45667 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131037 q = 1) : d101992 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131038 q = 1) : d101993 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131039 q = 1) : d101994 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131040 q = 1) : d101995 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d131041 q = 1) : d101996 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131041, d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45676 (p : Pattern) (ha : d129672 p = 1) (hb : d131047 p = 1) : d102002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131042 q = 1) : d101997 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131042, d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45675 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131043 q = 1) : d101998 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131043, d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131044 q = 1) : d101999 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131044, d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131045 q = 1) : d102000 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131045, d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131046 q = 1) : d102001 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131046, d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131047 q = 1) : d102002 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131047, d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45677 (p : Pattern) (ha : d129672 p = 1) (hb : d131053 p = 1) : d102008 p = 1 := by
  have h0 (q : Pattern) (ha : d129672 q = 1) (hb : d130970 q = 1) : d101925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45618 q ha hb
    | true =>
      simp only [d130970, d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45629 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130988 q = 1) : d101943 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130988, d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45640 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130989 q = 1) : d101944 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131007 q = 1) : d101962 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131007, d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45652 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131008 q = 1) : d101963 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131008, d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131009 q = 1) : d101964 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d131027 q = 1) : d101982 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131027, d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45664 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d131028 q = 1) : d101983 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131028, d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d131029 q = 1) : d101984 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131029, d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d131030 q = 1) : d101985 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d131048 q = 1) : d102003 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131048, d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45676 q ha hb
  have h12 (q : Pattern) (ha : d129672 q = 1) (hb : d131049 q = 1) : d102004 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131049, d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d131050 q = 1) : d102005 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131050, d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129672 q = 1) (hb : d131051 q = 1) : d102006 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131051, d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d131052 q = 1) : d102007 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129672 q = 1) (hb : d131053 q = 1) : d102008 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45678 (p : Pattern) (ha : d129672 p = 1) (hb : d131059 p = 1) : d102014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131054 q = 1) : d102009 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45677 q ha hb
    | true =>
      simp only [d131054, d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131055 q = 1) : d102010 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131056 q = 1) : d102011 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131057 q = 1) : d102012 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131058 q = 1) : d102013 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131059 q = 1) : d102014 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45679 (p : Pattern) (ha : d129672 p = 1) (hb : d131065 p = 1) : d102020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131060 q = 1) : d102015 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45678 q ha hb
    | true =>
      simp only [d131060, d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131061 q = 1) : d102016 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131062 q = 1) : d102017 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131063 q = 1) : d102018 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131064 q = 1) : d102019 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131065 q = 1) : d102020 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45680 (p : Pattern) (ha : d129672 p = 1) (hb : d131071 p = 1) : d102026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131066 q = 1) : d102021 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45679 q ha hb
    | true =>
      simp only [d131066, d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d131067 q = 1) : d102022 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d131068 q = 1) : d102023 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d131069 q = 1) : d102024 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d131070 q = 1) : d102025 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131070, d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d131071 q = 1) : d102026 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131071, d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45681 (p : Pattern) (ha : d130482 p = 1) (hb : d131077 p = 1) : d102032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d131072 q = 1) : d102027 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45680 q ha hb
    | true =>
      simp only [d131072, d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d131073 q = 1) : d102028 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130482, d131073, d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130482, d131073, d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d131074 q = 1) : d102029 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131074, d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d131075 q = 1) : d102030 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131075, d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d130482 q = 1) (hb : d131076 q = 1) : d102031 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131076, d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d130482 q = 1) (hb : d131077 q = 1) : d102032 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131077, d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro45682 (p : Pattern) (ha : d130482 p = 1) (hb : d131083 p = 1) : d102038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130482 q = 1) (hb : d131078 q = 1) : d102033 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45681 q ha hb
    | true =>
      simp only [d131078, d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130482 q = 1) (hb : d131079 q = 1) : d102034 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d131080 q = 1) : d102035 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130482 q = 1) (hb : d131081 q = 1) : d102036 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d131082 q = 1) : d102037 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d131083 q = 1) : d102038 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45683 (p : Pattern) (ha : d130482 p = 1) (hb : d131089 p = 1) : d102044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130482 q = 1) (hb : d131084 q = 1) : d102039 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45682 q ha hb
    | true =>
      simp only [d131084, d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130482 q = 1) (hb : d131085 q = 1) : d102040 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d131086 q = 1) : d102041 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130482 q = 1) (hb : d131087 q = 1) : d102042 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d131088 q = 1) : d102043 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d131089 q = 1) : d102044 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45684 (p : Pattern) (ha : d130482 p = 1) (hb : d131095 p = 1) : d102050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130482 q = 1) (hb : d131090 q = 1) : d102045 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45683 q ha hb
    | true =>
      simp only [d131090, d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130482 q = 1) (hb : d131091 q = 1) : d102046 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d131092 q = 1) : d102047 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130482 q = 1) (hb : d131093 q = 1) : d102048 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d131094 q = 1) : d102049 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d131095 q = 1) : d102050 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45685 (p : Pattern) (ha : d129672 p = 1) (hb : d192722 p = 1) : d129477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d129672 q = 1) : d9437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45612 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192718 q = 1) : d129473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192718, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192718, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192719 q = 1) : d129474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192719, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192719, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192720 q = 1) : d129475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192720, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192720, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192721 q = 1) : d129476 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192721, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192721, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192722 q = 1) : d129477 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192722, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192722, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45686 (p : Pattern) (ha : d129672 p = 1) (hb : d192732 p = 1) : d129487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d129672 q = 1) : d9342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45609 q ha hb
    | true =>
      simp only [d20420, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45605 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192728 q = 1) : d129483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192728, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192728, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192729 q = 1) : d129484 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192729, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192729, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192730 q = 1) : d129485 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192730, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192730, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192731 q = 1) : d129486 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192731, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192731, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192732 q = 1) : d129487 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192732, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192732, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45687 (p : Pattern) (ha : d129672 p = 1) (hb : d192738 p = 1) : d129493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192733 q = 1) : d129488 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192733, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192733, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45686 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192734 q = 1) : d129489 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192734, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192734, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192735 q = 1) : d129490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192735, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192735, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192736 q = 1) : d129491 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192736, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192736, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192737 q = 1) : d129492 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192737, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192737, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192738 q = 1) : d129493 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192738, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192738, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45688 (p : Pattern) (ha : d129672 p = 1) (hb : d192744 p = 1) : d129499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192723 q = 1) : d129478 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192723, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192723, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45685 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192724 q = 1) : d129479 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192724, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192724, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192725 q = 1) : d129480 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192725, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192725, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192726 q = 1) : d129481 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192726, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192726, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192727 q = 1) : d129482 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192727, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192727, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192739 q = 1) : d129494 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192739, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192739, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45687 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d192740 q = 1) : d129495 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192740, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192740, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d192741 q = 1) : d129496 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192741, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192741, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d192742 q = 1) : d129497 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192742, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192742, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d192743 q = 1) : d129498 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192743, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192743, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d192744 q = 1) : d129499 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192744, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192744, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45689 (p : Pattern) (ha : d129672 p = 1) (hb : d192750 p = 1) : d129505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192745 q = 1) : d129500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192745, d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45625 q hb ha
    | true =>
      simp only [d192745, d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45620 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192746 q = 1) : d129501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192746, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192746, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192747 q = 1) : d129502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192747, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192747, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192748 q = 1) : d129503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192748, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192748, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192749 q = 1) : d129504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192749, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192749, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192750 q = 1) : d129505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192750, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192750, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45690 (p : Pattern) (ha : d129672 p = 1) (hb : d192756 p = 1) : d129511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192751 q = 1) : d129506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192751, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192751, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45689 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192752 q = 1) : d129507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192752, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192752, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192753 q = 1) : d129508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192753, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192753, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192754 q = 1) : d129509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192754, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192754, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192755 q = 1) : d129510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192755, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192755, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192756 q = 1) : d129511 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192756, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192756, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45691 (p : Pattern) (ha : d129672 p = 1) (hb : d192762 p = 1) : d129517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192757 q = 1) : d129512 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192757, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192757, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45690 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192758 q = 1) : d129513 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192758, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192758, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192759 q = 1) : d129514 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192759, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192759, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192760 q = 1) : d129515 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192760, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192760, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192761 q = 1) : d129516 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192761, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192761, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192762 q = 1) : d129517 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192762, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192762, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45692 (p : Pattern) (ha : d129672 p = 1) (hb : d192769 p = 1) : d129524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192764 q = 1) : d129519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192764, d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45636 q hb ha
    | true =>
      simp only [d192764, d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45631 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192765 q = 1) : d129520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192765, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192765, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192766 q = 1) : d129521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192766, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192766, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192767 q = 1) : d129522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192767, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192767, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192768 q = 1) : d129523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192768, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192768, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192769 q = 1) : d129524 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192769, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192769, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45693 (p : Pattern) (ha : d129672 p = 1) (hb : d192775 p = 1) : d129530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192770 q = 1) : d129525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192770, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192770, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45692 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192771 q = 1) : d129526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192771, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192771, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192772 q = 1) : d129527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192772, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192772, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192773 q = 1) : d129528 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192773, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192773, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192774 q = 1) : d129529 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192774, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192774, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192775 q = 1) : d129530 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192775, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192775, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45694 (p : Pattern) (ha : d129672 p = 1) (hb : d192781 p = 1) : d129536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192776 q = 1) : d129531 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192776, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192776, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45693 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192777 q = 1) : d129532 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192777, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192777, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192778 q = 1) : d129533 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192778, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192778, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192779 q = 1) : d129534 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192779, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192779, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192780 q = 1) : d129535 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192780, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192780, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192781 q = 1) : d129536 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192781, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192781, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45695 (p : Pattern) (ha : d129672 p = 1) (hb : d192784 p = 1) : d129540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16674 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16675 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16693 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16694 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16694, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16695 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16696 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d171139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129539 q = 1) (hb : d129672 q = 1) : d129539 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d192784 q = 1) : d129540 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192784, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d192784, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro45696 (p : Pattern) (ha : d129672 p = 1) (hb : d192790 p = 1) : d129546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192785 q = 1) : d129541 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192785, d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45695 q ha hb
    | true =>
      simp only [d192785, d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192786 q = 1) : d129542 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192786, d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192786, d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d129672 q = 1) : d9876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45641 q ha hb
    | true =>
      simp only [d20638, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d129672 q = 1) : d9877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192787 q = 1) : d129543 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192787, d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192787, d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192788 q = 1) : d129544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192788, d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192788, d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d192789 q = 1) : d129545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192789, d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192789, d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d192790 q = 1) : d129546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192790, d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192790, d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45697 (p : Pattern) (ha : d129672 p = 1) (hb : d192796 p = 1) : d129552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192791 q = 1) : d129547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192791, d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45696 q ha hb
    | true =>
      simp only [d192791, d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45642 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192792 q = 1) : d129548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192792, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192792, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192793 q = 1) : d129549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192793, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192793, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192794 q = 1) : d129550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192794, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192794, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192795 q = 1) : d129551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192795, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192795, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192796 q = 1) : d129552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192796, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192796, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45698 (p : Pattern) (ha : d129672 p = 1) (hb : d192802 p = 1) : d129558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192797 q = 1) : d129553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192797, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192797, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45697 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192798 q = 1) : d129554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192798, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192798, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192799 q = 1) : d129555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192799, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192799, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192800 q = 1) : d129556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192800, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192800, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192801 q = 1) : d129557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192801, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192801, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192802 q = 1) : d129558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192802, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192802, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45699 (p : Pattern) (ha : d129672 p = 1) (hb : d192808 p = 1) : d129564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192803 q = 1) : d129559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192803, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192803, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45698 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192804 q = 1) : d129560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192804, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192804, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192805 q = 1) : d129561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192805, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192805, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192806 q = 1) : d129562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192806, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192806, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192807 q = 1) : d129563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192807, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192807, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192808 q = 1) : d129564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192808, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192808, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45700 (p : Pattern) (ha : d129672 p = 1) (hb : d192812 p = 1) : d129569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17034 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17035 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17053 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17054 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17054, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17055 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17056 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d171176 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129568 q = 1) (hb : d129672 q = 1) : d129568 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d192812 q = 1) : d129569 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192812, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d192812, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro45701 (p : Pattern) (ha : d129672 p = 1) (hb : d192818 p = 1) : d129575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192813 q = 1) : d129570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192813, d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45700 q ha hb
    | true =>
      simp only [d192813, d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192814 q = 1) : d129571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192814, d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192814, d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d129672 q = 1) : d10170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45653 q ha hb
    | true =>
      simp only [d20711, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d129672 q = 1) : d10171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192815 q = 1) : d129572 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192815, d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192815, d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192816 q = 1) : d129573 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192816, d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192816, d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d192817 q = 1) : d129574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192817, d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192817, d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d192818 q = 1) : d129575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192818, d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192818, d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45702 (p : Pattern) (ha : d129672 p = 1) (hb : d192824 p = 1) : d129581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192819 q = 1) : d129576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192819, d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45701 q ha hb
    | true =>
      simp only [d192819, d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45654 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192820 q = 1) : d129577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192820, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192820, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192821 q = 1) : d129578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192821, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192821, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192822 q = 1) : d129579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192822, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192822, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192823 q = 1) : d129580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192823, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192823, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192824 q = 1) : d129581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192824, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192824, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45703 (p : Pattern) (ha : d129672 p = 1) (hb : d192830 p = 1) : d129587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192825 q = 1) : d129582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192825, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192825, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45702 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192826 q = 1) : d129583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192826, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192826, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192827 q = 1) : d129584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192827, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192827, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192828 q = 1) : d129585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192828, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192828, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192829 q = 1) : d129586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192829, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192829, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192830 q = 1) : d129587 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192830, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192830, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45704 (p : Pattern) (ha : d129672 p = 1) (hb : d192836 p = 1) : d129593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192831 q = 1) : d129588 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192831, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192831, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45703 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192832 q = 1) : d129589 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192832, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192832, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192833 q = 1) : d129590 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192833, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192833, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192834 q = 1) : d129591 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192834, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192834, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192835 q = 1) : d129592 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192835, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192835, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192836 q = 1) : d129593 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192836, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192836, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45705 (p : Pattern) (ha : d129672 p = 1) (hb : d192841 p = 1) : d129599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17398 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17399 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17417 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17418 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17418, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17419 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17420 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d171214 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129598 q = 1) (hb : d129672 q = 1) : d129598 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d192841 q = 1) : d129599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192841, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d192841, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro45706 (p : Pattern) (ha : d129672 p = 1) (hb : d192847 p = 1) : d129605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192842 q = 1) : d129600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192842, d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45705 q ha hb
    | true =>
      simp only [d192842, d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192843 q = 1) : d129601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192843, d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192843, d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d129672 q = 1) : d10447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45665 q ha hb
    | true =>
      simp only [d20785, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d129672 q = 1) : d10448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192844 q = 1) : d129602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192844, d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192844, d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192845 q = 1) : d129603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192845, d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192845, d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d192846 q = 1) : d129604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192846, d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192846, d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d192847 q = 1) : d129605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192847, d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192847, d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45707 (p : Pattern) (ha : d129672 p = 1) (hb : d192853 p = 1) : d129611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192848 q = 1) : d129606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192848, d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45706 q ha hb
    | true =>
      simp only [d192848, d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45666 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192849 q = 1) : d129607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192849, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192849, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192850 q = 1) : d129608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192850, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192850, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192851 q = 1) : d129609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192851, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192851, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192852 q = 1) : d129610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192852, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192852, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192853 q = 1) : d129611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192853, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192853, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45708 (p : Pattern) (ha : d129672 p = 1) (hb : d192859 p = 1) : d129617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192854 q = 1) : d129612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192854, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192854, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45707 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192855 q = 1) : d129613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192855, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192855, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192856 q = 1) : d129614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192856, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192856, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192857 q = 1) : d129615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192857, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192857, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192858 q = 1) : d129616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192858, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192858, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192859 q = 1) : d129617 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192859, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192859, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45709 (p : Pattern) (ha : d129672 p = 1) (hb : d192865 p = 1) : d129623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192860 q = 1) : d129618 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192860, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192860, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45708 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192861 q = 1) : d129619 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192861, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192861, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192862 q = 1) : d129620 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192862, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192862, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192863 q = 1) : d129621 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192863, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192863, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192864 q = 1) : d129622 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192864, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192864, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192865 q = 1) : d129623 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192865, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192865, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45710 (p : Pattern) (ha : d129672 p = 1) (hb : d192871 p = 1) : d129629 p = 1 := by
  have h0 (q : Pattern) (ha : d129672 q = 1) (hb : d192763 q = 1) : d129518 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192763, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45688 q ha hb
    | true =>
      simp only [d192763, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45691 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192782 q = 1) : d129537 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192782, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192782, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45694 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192783 q = 1) : d129538 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192783, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192783, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192809 q = 1) : d129565 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192809, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192809, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45699 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192810 q = 1) : d129566 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192810, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192810, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192811 q = 1) : d129567 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192811, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192811, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d192837 q = 1) : d129594 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192837, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192837, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45704 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d192838 q = 1) : d129595 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192838, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192838, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d192839 q = 1) : d129596 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192839, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192839, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d192840 q = 1) : d129597 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192840, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192840, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d192866 q = 1) : d129624 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192866, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192866, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45709 q ha hb
  have h12 (q : Pattern) (ha : d129672 q = 1) (hb : d192867 q = 1) : d129625 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192867, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192867, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d192868 q = 1) : d129626 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192868, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192868, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129672 q = 1) (hb : d192869 q = 1) : d129627 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192869, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192869, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d192870 q = 1) : d129628 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d192870, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d192870, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129672 q = 1) (hb : d192871 q = 1) : d129629 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d192871, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d192871, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45711 (p : Pattern) (ha : d129672 p = 1) (hb : d192877 p = 1) : d129635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192872 q = 1) : d129630 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d192872, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45710 q ha hb
    | true =>
      simp only [d192872, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192873 q = 1) : d129631 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d192873, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192873, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192874 q = 1) : d129632 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d192874, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192874, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192875 q = 1) : d129633 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d192875, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192875, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192876 q = 1) : d129634 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d192876, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192876, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192877 q = 1) : d129635 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d192877, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192877, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45712 (p : Pattern) (ha : d129672 p = 1) (hb : d192883 p = 1) : d129641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192878 q = 1) : d129636 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d192878, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45711 q ha hb
    | true =>
      simp only [d192878, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192879 q = 1) : d129637 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d192879, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192879, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192880 q = 1) : d129638 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d192880, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192880, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192881 q = 1) : d129639 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d192881, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192881, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192882 q = 1) : d129640 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d192882, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192882, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192883 q = 1) : d129641 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d192883, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192883, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45713 (p : Pattern) (ha : d129672 p = 1) (hb : d192889 p = 1) : d129647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192884 q = 1) : d129642 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45712 q ha hb
    | true =>
      simp only [d192884, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d192885 q = 1) : d129643 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d192886 q = 1) : d129644 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d192887 q = 1) : d129645 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d192887, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192887, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d192888 q = 1) : d129646 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192888, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192888, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d192889 q = 1) : d129647 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192889, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45714 (p : Pattern) (ha : d130482 p = 1) (hb : d192895 p = 1) : d129653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d192890 q = 1) : d129648 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45713 q ha hb
    | true =>
      simp only [d192890, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d192891 q = 1) : d129649 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130482, d192891, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130482, d192891, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d192892 q = 1) : d129650 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192892, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d192893 q = 1) : d129651 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192893, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d130482 q = 1) (hb : d192894 q = 1) : d129652 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192894, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d130482 q = 1) (hb : d192895 q = 1) : d129653 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192895, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro45715 (p : Pattern) (ha : d130482 p = 1) (hb : d192901 p = 1) : d129659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130482 q = 1) (hb : d192896 q = 1) : d129654 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45714 q ha hb
    | true =>
      simp only [d192896, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130482 q = 1) (hb : d192897 q = 1) : d129655 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d192898 q = 1) : d129656 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130482 q = 1) (hb : d192899 q = 1) : d129657 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d192900 q = 1) : d129658 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d192901 q = 1) : d129659 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45716 (p : Pattern) (ha : d130482 p = 1) (hb : d192907 p = 1) : d129665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130482 q = 1) (hb : d192902 q = 1) : d129660 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45715 q ha hb
    | true =>
      simp only [d192902, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130482 q = 1) (hb : d192903 q = 1) : d129661 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d192904 q = 1) : d129662 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130482 q = 1) (hb : d192905 q = 1) : d129663 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d192906 q = 1) : d129664 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d192907 q = 1) : d129665 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45717 (p : Pattern) (ha : d130482 p = 1) (hb : d192913 p = 1) : d129671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130482 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130482 q = 1) (hb : d192908 q = 1) : d129666 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45716 q ha hb
    | true =>
      simp only [d192908, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130482 q = 1) (hb : d192909 q = 1) : d129667 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130482 q = 1) (hb : d192910 q = 1) : d129668 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130482 q = 1) (hb : d192911 q = 1) : d129669 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130482 q = 1) (hb : d192912 q = 1) : d129670 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130482 q = 1) (hb : d192913 q = 1) : d129671 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45718 (p : Pattern) (ha : d131095 p = 1) (hb : d194332 p = 1) : d131095 p = 1 := by
  have h0 (q : Pattern) (ha : d131095 q = 1) (hb : d194332 q = 1) : d131095 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro45719 (p : Pattern) (ha : d192913 p = 1) (hb : d194332 p = 1) : d192913 p = 1 := by
  have h0 (q : Pattern) (ha : d192913 q = 1) (hb : d194332 q = 1) : d192913 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro45720 (p : Pattern) (ha : d74849 p = 1) (hb : d194333 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d194333 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro45721 (p : Pattern) (ha : d53865 p = 1) (hb : d194333 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d194333 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro45722 (p : Pattern) (ha : d74849 p = 1) (hb : d194337 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d194337 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro45723 (p : Pattern) (ha : d53865 p = 1) (hb : d194337 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d194337 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro45724 (p : Pattern) (ha : d20893 p = 1) (hb : d146836 p = 1) : d148547 p = 1 := by
  have h0 (q : Pattern) (ha : d20892 q = 1) (hb : d116750 q = 1) : d20892 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20893 q = 1) (hb : d146836 q = 1) : d148547 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d146836, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20893, d146836, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45725 (p : Pattern) (ha : d20899 p = 1) (hb : d146836 p = 1) : d151290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d146836 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20897 q = 1) (hb : d146836 q = 1) : d151288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20897, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d146836 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20898 q = 1) (hb : d146836 q = 1) : d151289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d151289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20898, d151289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20899 q = 1) (hb : d146836 q = 1) : d151290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d151290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20899, d151290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro45726 (p : Pattern) (ha : d20905 p = 1) (hb : d146836 p = 1) : d151296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d146836 q = 1) : d151295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20905 q = 1) (hb : d146836 q = 1) : d151296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d151296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d151296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45727 (p : Pattern) (ha : d146836 p = 1) (hb : d150001 p = 1) : d151302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d146836 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d146836 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20906 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
    | true =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d149997 q = 1) : d151298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d149997, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146836 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d149998 q = 1) : d151299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d149999 q = 1) : d151300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d149999, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150000 q = 1) : d151301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150000, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150001 q = 1) : d151302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d151302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150001, d151302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45728 (p : Pattern) (ha : d20912 p = 1) (hb : d146836 p = 1) : d151303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d146836 q = 1) : d151295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20912 q = 1) (hb : d146836 q = 1) : d151303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d151303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20912, d151303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45729 (p : Pattern) (ha : d146836 p = 1) (hb : d150006 p = 1) : d151309 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d146836 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d146836 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20906 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
    | true =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d149997 q = 1) : d151298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d149997, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146836 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d149998 q = 1) : d151299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d149999 q = 1) : d151300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d149999, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150000 q = 1) : d151301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150000, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d146836 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d146836 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20913 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45728 q ha hb
    | true =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150002 q = 1) : d151305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d150002, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d146836 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150003 q = 1) : d151306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150003, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150004 q = 1) : d151307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d151307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150004, d151307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146836 q = 1) (hb : d150005 q = 1) : d151308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d151308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150005, d151308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d146836 q = 1) (hb : d150006 q = 1) : d151309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d151309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150006, d151309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro45730 (p : Pattern) (ha : d146836 p = 1) (hb : d150013 p = 1) : d151316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45728 q ha hb
    | true =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150002 q = 1) : d151305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150002, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d146836 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150003 q = 1) : d151306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150003, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150011 q = 1) : d151314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d151314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150011, d151314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150012 q = 1) : d151315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d151315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150012, d151315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150013 q = 1) : d151316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d151316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150013, d151316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45731 (p : Pattern) (ha : d20932 p = 1) (hb : d146836 p = 1) : d148585 p = 1 := by
  have h0 (q : Pattern) (ha : d20931 q = 1) (hb : d116750 q = 1) : d20931 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20932 q = 1) (hb : d146836 q = 1) : d148585 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d146836, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20932, d146836, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45732 (p : Pattern) (ha : d20938 p = 1) (hb : d146836 p = 1) : d151327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d146836 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20936 q = 1) (hb : d146836 q = 1) : d151325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20936, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d146836 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20937 q = 1) (hb : d146836 q = 1) : d151326 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d151326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20937, d151326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20938 q = 1) (hb : d146836 q = 1) : d151327 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d151327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20938, d151327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro45733 (p : Pattern) (ha : d20944 p = 1) (hb : d146836 p = 1) : d151333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d146836 q = 1) : d151328 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45732 q ha hb
    | true =>
      simp only [d20939, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d146836 q = 1) : d151329 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d146836 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20941 q = 1) (hb : d146836 q = 1) : d151330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d151330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d151330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20942 q = 1) (hb : d146836 q = 1) : d151331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d151331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20942, d151331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20943 q = 1) (hb : d146836 q = 1) : d151332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d151332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20943, d151332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20944 q = 1) (hb : d146836 q = 1) : d151333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d151333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20944, d151333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45734 (p : Pattern) (ha : d146836 p = 1) (hb : d150023 p = 1) : d151339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146836 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d146836 q = 1) : d151334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45733 q ha hb
    | true =>
      simp only [d20945, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150019 q = 1) : d151335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d151335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150019, d151335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d146836 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150020 q = 1) : d151336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d151336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150020, d151336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150021 q = 1) : d151337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d151337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150021, d151337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150022 q = 1) : d151338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d151338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150022, d151338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150023 q = 1) : d151339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d151339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150023, d151339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45735 (p : Pattern) (ha : d146836 p = 1) (hb : d150029 p = 1) : d151345 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d146836 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150007 q = 1) : d151310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d151310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45727 q ha hb
    | true =>
      simp only [d150007, d151310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45729 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d146836 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150008 q = 1) : d151311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d151311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150008, d151311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150009 q = 1) : d151312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d151312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150009, d151312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150010 q = 1) : d151313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d151313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150010, d151313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150014 q = 1) : d151317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d151317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150014, d151317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45730 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150015 q = 1) : d151318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d151318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150015, d151318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150016 q = 1) : d151319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d151319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150016, d151319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150017 q = 1) : d151320 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d151320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150017, d151320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150018 q = 1) : d151321 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d151321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150018, d151321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150024 q = 1) : d151340 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d151340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150024, d151340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45734 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150025 q = 1) : d151341 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d151341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150025, d151341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150026 q = 1) : d151342 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d151342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150026, d151342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150027 q = 1) : d151343 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d151343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150027, d151343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150028 q = 1) : d151344 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d151344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150028, d151344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150029 q = 1) : d151345 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d151345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150029, d151345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45736 (p : Pattern) (ha : d20966 p = 1) (hb : d146836 p = 1) : d151355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
    | true =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d146836 q = 1) : d151351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d146836 q = 1) : d151352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d146836 q = 1) : d151353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d146836 q = 1) : d151354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20966 q = 1) (hb : d146836 q = 1) : d151355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45737 (p : Pattern) (ha : d20973 p = 1) (hb : d146836 p = 1) : d151362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
    | true =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d146836 q = 1) : d151351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d146836 q = 1) : d151352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d146836 q = 1) : d151353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d146836 q = 1) : d151354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20913 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45728 q ha hb
    | true =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20969 q = 1) (hb : d146836 q = 1) : d151358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20970 q = 1) (hb : d146836 q = 1) : d151359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20970, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20971 q = 1) (hb : d146836 q = 1) : d151360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20972 q = 1) (hb : d146836 q = 1) : d151361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20973 q = 1) (hb : d146836 q = 1) : d151362 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20973, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro45738 (p : Pattern) (ha : d21058 p = 1) (hb : d146836 p = 1) : d151422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
    | true =>
      simp only [d20906, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d146836 q = 1) : d151351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d146836 q = 1) : d151352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d146836 q = 1) : d151353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d146836 q = 1) : d151354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d146836 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21058 q = 1) (hb : d146836 q = 1) : d151422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d151422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21058, d151422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45739 (p : Pattern) (ha : d20978 p = 1) (hb : d146836 p = 1) : d151367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d146836 q = 1) : d151366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20978 q = 1) (hb : d146836 q = 1) : d151367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d151367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d151367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45740 (p : Pattern) (ha : d20985 p = 1) (hb : d146836 p = 1) : d151374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d146836 q = 1) : d151372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d146836 q = 1) : d151373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20985 q = 1) (hb : d146836 q = 1) : d151374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d151374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d151374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45741 (p : Pattern) (ha : d20996 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d20994 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20996 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20996, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45742 (p : Pattern) (ha : d21002 p = 1) (hb : d146836 p = 1) : d151383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d146836 q = 1) : d151378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d20997, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d146836 q = 1) : d151379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d146836 q = 1) : d151380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d146836 q = 1) : d151381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d146836 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20897 q = 1) (hb : d146836 q = 1) : d151288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20897, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21001 q = 1) (hb : d146836 q = 1) : d151382 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d151382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21001, d151382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21002 q = 1) (hb : d146836 q = 1) : d151383 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d151383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21002, d151383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro45743 (p : Pattern) (ha : d21008 p = 1) (hb : d146836 p = 1) : d151389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d146836 q = 1) : d151384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45742 q ha hb
    | true =>
      simp only [d21003, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d146836 q = 1) : d151385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d146836 q = 1) : d151386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d146836 q = 1) : d151387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d146836 q = 1) : d151388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d146836 q = 1) : d151389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d151389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d151389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45744 (p : Pattern) (ha : d21029 p = 1) (hb : d146836 p = 1) : d151395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d146836 q = 1) : d151392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d146836 q = 1) : d151393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d146836 q = 1) : d151394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d146836 q = 1) : d151395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d151395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d151395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45745 (p : Pattern) (ha : d146836 p = 1) (hb : d150039 p = 1) : d151401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146836 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d146836 q = 1) : d151368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45739 q ha hb
    | true =>
      simp only [d20979, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d146836 q = 1) : d151369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d146836 q = 1) : d151370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d146836 q = 1) : d151371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146836 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d146836 q = 1) : d151375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45740 q ha hb
    | true =>
      simp only [d20986, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d146836 q = 1) : d151376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d146836 q = 1) : d151377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d146836 q = 1) : d151390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45743 q ha hb
    | true =>
      simp only [d21009, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150035 q = 1) : d151391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150035, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d146836 q = 1) : d151396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45744 q ha hb
    | true =>
      simp only [d21030, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d146836 q = 1) : d151397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150036 q = 1) : d151398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150037 q = 1) : d151399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150037, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150038 q = 1) : d151400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150038, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150039 q = 1) : d151401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d151401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150039, d151401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45746 (p : Pattern) (ha : d21036 p = 1) (hb : d146836 p = 1) : d151402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d146836 q = 1) : d151366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21036 q = 1) (hb : d146836 q = 1) : d151402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d151402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21036, d151402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45747 (p : Pattern) (ha : d21041 p = 1) (hb : d146836 p = 1) : d151407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d146836 q = 1) : d151372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d146836 q = 1) : d151373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21041 q = 1) (hb : d146836 q = 1) : d151407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d151407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21041, d151407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45748 (p : Pattern) (ha : d21045 p = 1) (hb : d146836 p = 1) : d151411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d146836 q = 1) : d151384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45742 q ha hb
    | true =>
      simp only [d21003, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d146836 q = 1) : d151385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d146836 q = 1) : d151386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d146836 q = 1) : d151387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d146836 q = 1) : d151388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d146836 q = 1) : d151411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d151411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d151411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45749 (p : Pattern) (ha : d21050 p = 1) (hb : d146836 p = 1) : d151414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45725 q ha hb
    | true =>
      simp only [d20900, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d146836 q = 1) : d151392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d146836 q = 1) : d151393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d146836 q = 1) : d151394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d146836 q = 1) : d151414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d151414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d151414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
