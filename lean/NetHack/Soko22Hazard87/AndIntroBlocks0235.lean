import NetHack.Soko22Hazard87.AndIntroBlocks0234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro58750 (p : Pattern) (ha : d231349 p = 1) (hb : d239127 p = 1) : d240181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231344 q = 1) (hb : d239126 q = 1) : d240176 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d231344, d240176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58749 q ha hb
    | true =>
      simp only [d231344, d240176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231345 q = 1) (hb : d239126 q = 1) : d240177 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d231345, d240177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231345, d240177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231346 q = 1) (hb : d239126 q = 1) : d240178 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d231346, d240178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231346, d240178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231347 q = 1) (hb : d239126 q = 1) : d240179 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d231347, d240179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231347, d240179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231348 q = 1) (hb : d239126 q = 1) : d240180 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d231348, d240180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231348, d240180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d231349 q = 1) (hb : d239127 q = 1) : d240181 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d231349, d239127, d240181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231349, d239127, d240181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58751 (p : Pattern) (ha : d231355 p = 1) (hb : d239127 p = 1) : d240187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231350 q = 1) (hb : d239127 q = 1) : d240182 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d231350, d240182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58750 q ha hb
    | true =>
      simp only [d231350, d240182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231351 q = 1) (hb : d239127 q = 1) : d240183 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d231351, d240183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231351, d240183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231352 q = 1) (hb : d239127 q = 1) : d240184 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d231352, d240184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231352, d240184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231353 q = 1) (hb : d239127 q = 1) : d240185 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d231353, d240185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231353, d240185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231354 q = 1) (hb : d239127 q = 1) : d240186 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d231354, d240186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231354, d240186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231355 q = 1) (hb : d239127 q = 1) : d240187 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d231355, d240187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231355, d240187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58752 (p : Pattern) (ha : d231361 p = 1) (hb : d239127 p = 1) : d240193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231356 q = 1) (hb : d239127 q = 1) : d240188 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d231356, d240188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58751 q ha hb
    | true =>
      simp only [d231356, d240188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231357 q = 1) (hb : d239127 q = 1) : d240189 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d231357, d240189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231357, d240189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231358 q = 1) (hb : d239127 q = 1) : d240190 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d231358, d240190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231358, d240190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231359 q = 1) (hb : d239127 q = 1) : d240191 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d231359, d240191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231359, d240191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231360 q = 1) (hb : d239127 q = 1) : d240192 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d231360, d240192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231360, d240192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231361 q = 1) (hb : d239127 q = 1) : d240193 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d231361, d240193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231361, d240193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58753 (p : Pattern) (ha : d231367 p = 1) (hb : d239127 p = 1) : d240199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231362 q = 1) (hb : d239127 q = 1) : d240194 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d231362, d240194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58752 q ha hb
    | true =>
      simp only [d231362, d240194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231363 q = 1) (hb : d239127 q = 1) : d240195 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d231363, d240195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231363, d240195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231364 q = 1) (hb : d239127 q = 1) : d240196 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d231364, d240196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231364, d240196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231365 q = 1) (hb : d239127 q = 1) : d240197 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d231365, d240197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231365, d240197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231366 q = 1) (hb : d239127 q = 1) : d240198 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d231366, d240198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231366, d240198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231367 q = 1) (hb : d239127 q = 1) : d240199 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d231367, d240199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231367, d240199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58754 (p : Pattern) (ha : d231373 p = 1) (hb : d239127 p = 1) : d240205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231368 q = 1) (hb : d239127 q = 1) : d240200 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d231368, d240200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58753 q ha hb
    | true =>
      simp only [d231368, d240200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231369 q = 1) (hb : d239127 q = 1) : d240201 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d231369, d240201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231369, d240201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231370 q = 1) (hb : d239127 q = 1) : d240202 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d231370, d240202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231370, d240202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231371 q = 1) (hb : d239127 q = 1) : d240203 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d231371, d240203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231371, d240203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231372 q = 1) (hb : d239127 q = 1) : d240204 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d231372, d240204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231372, d240204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231373 q = 1) (hb : d239127 q = 1) : d240205 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d231373, d240205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231373, d240205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58755 (p : Pattern) (ha : d231379 p = 1) (hb : d239127 p = 1) : d240211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231374 q = 1) (hb : d239127 q = 1) : d240206 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d231374, d240206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58754 q ha hb
    | true =>
      simp only [d231374, d240206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231375 q = 1) (hb : d239127 q = 1) : d240207 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d231375, d240207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231375, d240207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231376 q = 1) (hb : d239127 q = 1) : d240208 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d231376, d240208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231376, d240208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231377 q = 1) (hb : d239127 q = 1) : d240209 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d231377, d240209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231377, d240209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231378 q = 1) (hb : d239127 q = 1) : d240210 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d231378, d240210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231378, d240210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231379 q = 1) (hb : d239127 q = 1) : d240211 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d231379, d240211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231379, d240211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58756 (p : Pattern) (ha : d1 p = 1) (hb : d240211 p = 1) : d240211 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d240211 q = 1) : d240211 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro58757 (p : Pattern) (ha : d0 p = 1) (hb : d240211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d240211 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro58758 (p : Pattern) (ha : d9381 p = 1) (hb : d208034 p = 1) : d25221 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5449 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d208034 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9381 q = 1) (hb : d208034 q = 1) : d25221 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9381, d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58759 (p : Pattern) (ha : d16081 p = 1) (hb : d208034 p = 1) : d25461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d208034 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d208034 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d208034 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d208034 q = 1) : d25226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d208034 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d208034 q = 1) : d25461 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58760 (p : Pattern) (ha : d23140 p = 1) (hb : d208034 p = 1) : d240217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23135 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
    | true =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23136 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23137 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d208034 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23138 q = 1) (hb : d208034 q = 1) : d240215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23138, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23138, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d208034 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23139 q = 1) (hb : d208034 q = 1) : d240216 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23139, d240216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23139, d240216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23140 q = 1) (hb : d208034 q = 1) : d240217 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23140, d240217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23140, d240217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro58761 (p : Pattern) (ha : d23146 p = 1) (hb : d208034 p = 1) : d240223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23145 q = 1) (hb : d208034 q = 1) : d240222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23145, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23145, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23146 q = 1) (hb : d208034 q = 1) : d240223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23146, d240223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23146, d240223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58762 (p : Pattern) (ha : d208034 p = 1) (hb : d211086 p = 1) : d240229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d208034 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d208034 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23147 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
    | true =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211082 q = 1) : d240225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211082, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211082, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208034 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211083 q = 1) : d240226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211083, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211083, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211084 q = 1) : d240227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211084, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211084, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211085 q = 1) : d240228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211085, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211085, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211086 q = 1) : d240229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211086, d240229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211086, d240229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58763 (p : Pattern) (ha : d23153 p = 1) (hb : d208034 p = 1) : d240230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23145 q = 1) (hb : d208034 q = 1) : d240222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23145, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23145, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23153 q = 1) (hb : d208034 q = 1) : d240230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23153, d240230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23153, d240230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro58764 (p : Pattern) (ha : d208034 p = 1) (hb : d211091 p = 1) : d240236 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d208034 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d208034 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23147 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
    | true =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211082 q = 1) : d240225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211082, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211082, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208034 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211083 q = 1) : d240226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211083, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211083, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211084 q = 1) : d240227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211084, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211084, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211085 q = 1) : d240228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211085, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211085, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d208034 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d208034 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23154 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58763 q ha hb
    | true =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211087 q = 1) : d240232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211087, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d211087, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d208034 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211088 q = 1) : d240233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211088, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211088, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211089 q = 1) : d240234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211089, d240234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211089, d240234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208034 q = 1) (hb : d211090 q = 1) : d240235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211090, d240235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211090, d240235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d208034 q = 1) (hb : d211091 q = 1) : d240236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211091, d240236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211091, d240236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58765 (p : Pattern) (ha : d208034 p = 1) (hb : d211098 p = 1) : d240243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58763 q ha hb
    | true =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211087 q = 1) : d240232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211087, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211087, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d208034 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211088 q = 1) : d240233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211088, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211088, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211096 q = 1) : d240241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211096, d240241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211096, d240241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211097 q = 1) : d240242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211097, d240242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211097, d240242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211098 q = 1) : d240243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211098, d240243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211098, d240243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58766 (p : Pattern) (ha : d16166 p = 1) (hb : d208034 p = 1) : d25595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d208034 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d208034 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d208034 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d208034 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d208034 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d208034 q = 1) : d25318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d208034 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d208034 q = 1) : d25595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58767 (p : Pattern) (ha : d23177 p = 1) (hb : d208034 p = 1) : d240254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23172 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
    | true =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23173 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23174 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d208034 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23175 q = 1) (hb : d208034 q = 1) : d240252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23175, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23175, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d208034 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23176 q = 1) (hb : d208034 q = 1) : d240253 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23176, d240253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23176, d240253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23177 q = 1) (hb : d208034 q = 1) : d240254 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23177, d240254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23177, d240254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro58768 (p : Pattern) (ha : d23183 p = 1) (hb : d208034 p = 1) : d240260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23178 q = 1) (hb : d208034 q = 1) : d240255 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58767 q ha hb
    | true =>
      simp only [d23178, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23179 q = 1) (hb : d208034 q = 1) : d240256 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d208034 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23180 q = 1) (hb : d208034 q = 1) : d240257 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23180, d240257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23180, d240257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23181 q = 1) (hb : d208034 q = 1) : d240258 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23181, d240258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23181, d240258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23182 q = 1) (hb : d208034 q = 1) : d240259 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23182, d240259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23182, d240259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23183 q = 1) (hb : d208034 q = 1) : d240260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23183, d240260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23183, d240260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro58769 (p : Pattern) (ha : d208034 p = 1) (hb : d211108 p = 1) : d240266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208034 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d208034 q = 1) : d240261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58768 q ha hb
    | true =>
      simp only [d23184, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211104 q = 1) : d240262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211104, d240262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211104, d240262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d208034 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211105 q = 1) : d240263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211105, d240263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211105, d240263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211106 q = 1) : d240264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211106, d240264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211106, d240264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211107 q = 1) : d240265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211107, d240265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211107, d240265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211108 q = 1) : d240266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211108, d240266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211108, d240266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58770 (p : Pattern) (ha : d208034 p = 1) (hb : d211114 p = 1) : d240272 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d208034 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d211092 q = 1) : d240237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211092, d240237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58762 q ha hb
    | true =>
      simp only [d211092, d240237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58764 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d208034 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211093 q = 1) : d240238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211093, d240238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211093, d240238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211094 q = 1) : d240239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211094, d240239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211094, d240239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211095 q = 1) : d240240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211095, d240240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211095, d240240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211099 q = 1) : d240244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211099, d240244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211099, d240244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58765 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211100 q = 1) : d240245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211100, d240245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211100, d240245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211101 q = 1) : d240246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211101, d240246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211101, d240246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211102 q = 1) : d240247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211102, d240247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211102, d240247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211103 q = 1) : d240248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211103, d240248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211103, d240248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211109 q = 1) : d240267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211109, d240267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211109, d240267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58769 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211110 q = 1) : d240268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211110, d240268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211110, d240268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211111 q = 1) : d240269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211111, d240269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211111, d240269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211112 q = 1) : d240270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211112, d240270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211112, d240270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211113 q = 1) : d240271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211113, d240271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211113, d240271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211114 q = 1) : d240272 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211114, d240272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211114, d240272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro58771 (p : Pattern) (ha : d23205 p = 1) (hb : d208034 p = 1) : d240282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
    | true =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d208034 q = 1) : d240278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d208034 q = 1) : d240279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d208034 q = 1) : d240280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d208034 q = 1) : d240281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23205 q = 1) (hb : d208034 q = 1) : d240282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58772 (p : Pattern) (ha : d23212 p = 1) (hb : d208034 p = 1) : d240289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
    | true =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d208034 q = 1) : d240278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d208034 q = 1) : d240279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d208034 q = 1) : d240280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d208034 q = 1) : d240281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23154 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58763 q ha hb
    | true =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23208 q = 1) (hb : d208034 q = 1) : d240285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23208, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23209 q = 1) (hb : d208034 q = 1) : d240286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23209, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23210 q = 1) (hb : d208034 q = 1) : d240287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23211 q = 1) (hb : d208034 q = 1) : d240288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23212 q = 1) (hb : d208034 q = 1) : d240289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23212, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro58773 (p : Pattern) (ha : d23297 p = 1) (hb : d208034 p = 1) : d240350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
    | true =>
      simp only [d23147, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d208034 q = 1) : d240278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d208034 q = 1) : d240279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d208034 q = 1) : d240280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d208034 q = 1) : d240281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d208034 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23297 q = 1) (hb : d208034 q = 1) : d240350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23297, d240350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23297, d240350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58774 (p : Pattern) (ha : d23217 p = 1) (hb : d208034 p = 1) : d240294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23216 q = 1) (hb : d208034 q = 1) : d240293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23216, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23216, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23217 q = 1) (hb : d208034 q = 1) : d240294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23217, d240294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23217, d240294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58775 (p : Pattern) (ha : d23224 p = 1) (hb : d208034 p = 1) : d240301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23222 q = 1) (hb : d208034 q = 1) : d240299 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23222, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23222, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23223 q = 1) (hb : d208034 q = 1) : d240300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23223, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23223, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23224 q = 1) (hb : d208034 q = 1) : d240301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23224, d240301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23224, d240301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58776 (p : Pattern) (ha : d23230 p = 1) (hb : d208034 p = 1) : d25451 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23228 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23228, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23229 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d5448 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d5449 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23230 q = 1) (hb : d208034 q = 1) : d25451 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23230, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23230, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58777 (p : Pattern) (ha : d23236 p = 1) (hb : d208034 p = 1) : d240305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9382 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9384 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12493 q = 1) (hb : d208034 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12494 q = 1) (hb : d208034 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23235 q = 1) (hb : d208034 q = 1) : d25456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23235, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d208034 q = 1) : d28 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12495 q = 1) (hb : d208034 q = 1) : d25226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23236 q = 1) (hb : d208034 q = 1) : d240305 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23236, d240305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23236, d240305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58778 (p : Pattern) (ha : d23242 p = 1) (hb : d208034 p = 1) : d240311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23237 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58777 q ha hb
    | true =>
      simp only [d23237, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
  have h2 (q : Pattern) (ha : d23238 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23239 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23135 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
    | true =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23136 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23137 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23240 q = 1) (hb : d208034 q = 1) : d240309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23240, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d208034 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23138 q = 1) (hb : d208034 q = 1) : d240215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23138, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23138, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23241 q = 1) (hb : d208034 q = 1) : d240310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23241, d240310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23241, d240310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23242 q = 1) (hb : d208034 q = 1) : d240311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23242, d240311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23242, d240311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro58779 (p : Pattern) (ha : d23248 p = 1) (hb : d208034 p = 1) : d240317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23243 q = 1) (hb : d208034 q = 1) : d240312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23243, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58778 q ha hb
    | true =>
      simp only [d23243, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23244 q = 1) (hb : d208034 q = 1) : d240313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23244, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23244, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23245 q = 1) (hb : d208034 q = 1) : d240314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23245, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23245, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23246 q = 1) (hb : d208034 q = 1) : d240315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23246, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23246, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23247 q = 1) (hb : d208034 q = 1) : d240316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23247, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23247, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23248 q = 1) (hb : d208034 q = 1) : d240317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23248, d240317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23248, d240317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58780 (p : Pattern) (ha : d23268 p = 1) (hb : d208034 p = 1) : d240323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23265 q = 1) (hb : d208034 q = 1) : d240320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23265, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23265, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23266 q = 1) (hb : d208034 q = 1) : d240321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23266, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23266, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23267 q = 1) (hb : d208034 q = 1) : d240322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23267, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23267, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23268 q = 1) (hb : d208034 q = 1) : d240323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23268, d240323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23268, d240323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58781 (p : Pattern) (ha : d208034 p = 1) (hb : d211124 p = 1) : d240329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208034 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23218 q = 1) (hb : d208034 q = 1) : d240295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23218, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58774 q ha hb
    | true =>
      simp only [d23218, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23219 q = 1) (hb : d208034 q = 1) : d240296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23219, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23219, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23220 q = 1) (hb : d208034 q = 1) : d240297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23220, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23220, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23221 q = 1) (hb : d208034 q = 1) : d240298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23221, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23221, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208034 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23225 q = 1) (hb : d208034 q = 1) : d240302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23225, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58775 q ha hb
    | true =>
      simp only [d23225, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23226 q = 1) (hb : d208034 q = 1) : d240303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23226, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23226, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23227 q = 1) (hb : d208034 q = 1) : d240304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23227, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23227, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23249 q = 1) (hb : d208034 q = 1) : d240318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23249, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58779 q ha hb
    | true =>
      simp only [d23249, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211120 q = 1) : d240319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211120, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d23269 q = 1) (hb : d208034 q = 1) : d240324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23269, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58780 q ha hb
    | true =>
      simp only [d23269, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23270 q = 1) (hb : d208034 q = 1) : d240325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23270, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23270, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211121 q = 1) : d240326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211121, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211122 q = 1) : d240327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211122, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211123 q = 1) : d240328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211123, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211124 q = 1) : d240329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211124, d240329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211124, d240329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro58782 (p : Pattern) (ha : d23275 p = 1) (hb : d208034 p = 1) : d240330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23216 q = 1) (hb : d208034 q = 1) : d240293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23216, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23216, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23275 q = 1) (hb : d208034 q = 1) : d240330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23275, d240330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23275, d240330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro58783 (p : Pattern) (ha : d23280 p = 1) (hb : d208034 p = 1) : d240335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23222 q = 1) (hb : d208034 q = 1) : d240299 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23222, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23222, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23223 q = 1) (hb : d208034 q = 1) : d240300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23223, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23223, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23280 q = 1) (hb : d208034 q = 1) : d240335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23280, d240335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23280, d240335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro58784 (p : Pattern) (ha : d23284 p = 1) (hb : d208034 p = 1) : d240339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23243 q = 1) (hb : d208034 q = 1) : d240312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23243, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58778 q ha hb
    | true =>
      simp only [d23243, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23244 q = 1) (hb : d208034 q = 1) : d240313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23244, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23244, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23245 q = 1) (hb : d208034 q = 1) : d240314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23245, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23245, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23246 q = 1) (hb : d208034 q = 1) : d240315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23246, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23246, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23247 q = 1) (hb : d208034 q = 1) : d240316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23247, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23247, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23284 q = 1) (hb : d208034 q = 1) : d240339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23284, d240339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23284, d240339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58785 (p : Pattern) (ha : d23289 p = 1) (hb : d208034 p = 1) : d240342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58760 q ha hb
    | true =>
      simp only [d23141, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23265 q = 1) (hb : d208034 q = 1) : d240320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23265, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23265, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23266 q = 1) (hb : d208034 q = 1) : d240321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23266, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23266, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23267 q = 1) (hb : d208034 q = 1) : d240322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23267, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23267, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23289 q = 1) (hb : d208034 q = 1) : d240342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23289, d240342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23289, d240342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58786 (p : Pattern) (ha : d208034 p = 1) (hb : d211129 p = 1) : d240348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208034 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23218 q = 1) (hb : d208034 q = 1) : d240295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23218, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58774 q ha hb
    | true =>
      simp only [d23218, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23219 q = 1) (hb : d208034 q = 1) : d240296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23219, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23219, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23220 q = 1) (hb : d208034 q = 1) : d240297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23220, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23220, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23221 q = 1) (hb : d208034 q = 1) : d240298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23221, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23221, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208034 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23225 q = 1) (hb : d208034 q = 1) : d240302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23225, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58775 q ha hb
    | true =>
      simp only [d23225, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23226 q = 1) (hb : d208034 q = 1) : d240303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23226, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23226, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23227 q = 1) (hb : d208034 q = 1) : d240304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23227, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23227, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23249 q = 1) (hb : d208034 q = 1) : d240318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23249, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58779 q ha hb
    | true =>
      simp only [d23249, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58761 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211120 q = 1) : d240319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211120, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d23269 q = 1) (hb : d208034 q = 1) : d240324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23269, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58780 q ha hb
    | true =>
      simp only [d23269, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23270 q = 1) (hb : d208034 q = 1) : d240325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23270, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23270, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211121 q = 1) : d240326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211121, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211122 q = 1) : d240327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211122, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211123 q = 1) : d240328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211123, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d208034 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d23276 q = 1) (hb : d208034 q = 1) : d240331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23276, d240331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58782 q ha hb
    | true =>
      simp only [d23276, d240331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23277 q = 1) (hb : d208034 q = 1) : d240332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23277, d240332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23277, d240332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d23278 q = 1) (hb : d208034 q = 1) : d240333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23278, d240333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23278, d240333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d23279 q = 1) (hb : d208034 q = 1) : d240334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23279, d240334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23279, d240334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d208034 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d23281 q = 1) (hb : d208034 q = 1) : d240336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23281, d240336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58783 q ha hb
    | true =>
      simp only [d23281, d240336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d23282 q = 1) (hb : d208034 q = 1) : d240337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23282, d240337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23282, d240337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d23283 q = 1) (hb : d208034 q = 1) : d240338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23283, d240338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23283, d240338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23285 q = 1) (hb : d208034 q = 1) : d240340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23285, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58784 q ha hb
    | true =>
      simp only [d23285, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58763 q ha hb
  have h27 (q : Pattern) (ha : d208034 q = 1) (hb : d211125 q = 1) : d240341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d211125, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d23290 q = 1) (hb : d208034 q = 1) : d240343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23290, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58785 q ha hb
    | true =>
      simp only [d23290, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d23291 q = 1) (hb : d208034 q = 1) : d240344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23291, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d23291, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d208034 q = 1) (hb : d211126 q = 1) : d240345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d211126, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d208034 q = 1) (hb : d211127 q = 1) : d240346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211127, d240346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d211127, d240346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d208034 q = 1) (hb : d211128 q = 1) : d240347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211128, d240347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211128, d240347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d208034 q = 1) (hb : d211129 q = 1) : d240348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211129, d240348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211129, d240348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro58787 (p : Pattern) (ha : d208034 p = 1) (hb : d211136 p = 1) : d240357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23285 q = 1) (hb : d208034 q = 1) : d240340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23285, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58784 q ha hb
    | true =>
      simp only [d23285, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58763 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211125 q = 1) : d240341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211125, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23290 q = 1) (hb : d208034 q = 1) : d240343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23290, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58785 q ha hb
    | true =>
      simp only [d23290, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23291 q = 1) (hb : d208034 q = 1) : d240344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23291, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23291, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211126 q = 1) : d240345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211126, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211134 q = 1) : d240355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211134, d240355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211134, d240355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211135 q = 1) : d240356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211135, d240356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211135, d240356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211136 q = 1) : d240357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211136, d240357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211136, d240357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58788 (p : Pattern) (ha : d23315 p = 1) (hb : d208034 p = 1) : d240363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12599 q = 1) (hb : d208034 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
  have h8 (q : Pattern) (ha : d9382 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12600 q = 1) (hb : d208034 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9384 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12601 q = 1) (hb : d208034 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12602 q = 1) (hb : d208034 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23314 q = 1) (hb : d208034 q = 1) : d25590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23314, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d208034 q = 1) : d69 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12603 q = 1) (hb : d208034 q = 1) : d25318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23315 q = 1) (hb : d208034 q = 1) : d240363 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23315, d240363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23315, d240363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro58789 (p : Pattern) (ha : d23321 p = 1) (hb : d208034 p = 1) : d240369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23316 q = 1) (hb : d208034 q = 1) : d240364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58788 q ha hb
    | true =>
      simp only [d23316, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
  have h2 (q : Pattern) (ha : d23317 q = 1) (hb : d208034 q = 1) : d240365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23318 q = 1) (hb : d208034 q = 1) : d240366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23172 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
    | true =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23173 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23174 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23319 q = 1) (hb : d208034 q = 1) : d240367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23319, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d208034 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23175 q = 1) (hb : d208034 q = 1) : d240252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23175, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23175, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23320 q = 1) (hb : d208034 q = 1) : d240368 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23320, d240368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23320, d240368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23321 q = 1) (hb : d208034 q = 1) : d240369 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23321, d240369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23321, d240369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro58790 (p : Pattern) (ha : d23327 p = 1) (hb : d208034 p = 1) : d240375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23322 q = 1) (hb : d208034 q = 1) : d240370 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23322, d240370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58789 q ha hb
    | true =>
      simp only [d23322, d240370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23323 q = 1) (hb : d208034 q = 1) : d240371 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23323, d240371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23323, d240371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23178 q = 1) (hb : d208034 q = 1) : d240255 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58767 q ha hb
    | true =>
      simp only [d23178, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23179 q = 1) (hb : d208034 q = 1) : d240256 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23324 q = 1) (hb : d208034 q = 1) : d240372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23324, d240372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23324, d240372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23325 q = 1) (hb : d208034 q = 1) : d240373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23325, d240373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23325, d240373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23326 q = 1) (hb : d208034 q = 1) : d240374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23326, d240374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23326, d240374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23327 q = 1) (hb : d208034 q = 1) : d240375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23327, d240375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23327, d240375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58791 (p : Pattern) (ha : d23347 p = 1) (hb : d208034 p = 1) : d240381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23178 q = 1) (hb : d208034 q = 1) : d240255 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58767 q ha hb
    | true =>
      simp only [d23178, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23179 q = 1) (hb : d208034 q = 1) : d240256 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23344 q = 1) (hb : d208034 q = 1) : d240378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23344, d240378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23344, d240378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23345 q = 1) (hb : d208034 q = 1) : d240379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23345, d240379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23345, d240379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23346 q = 1) (hb : d208034 q = 1) : d240380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23346, d240380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23346, d240380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23347 q = 1) (hb : d208034 q = 1) : d240381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23347, d240381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23347, d240381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58792 (p : Pattern) (ha : d208034 p = 1) (hb : d211146 p = 1) : d240387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23328 q = 1) (hb : d208034 q = 1) : d240376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23328, d240376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58790 q ha hb
    | true =>
      simp only [d23328, d240376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58768 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211142 q = 1) : d240377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211142, d240377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211142, d240377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23348 q = 1) (hb : d208034 q = 1) : d240382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23348, d240382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58791 q ha hb
    | true =>
      simp only [d23348, d240382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23349 q = 1) (hb : d208034 q = 1) : d240383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23349, d240383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23349, d240383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211143 q = 1) : d240384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211143, d240384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211143, d240384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211144 q = 1) : d240385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211144, d240385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211144, d240385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211145 q = 1) : d240386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211145, d240386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211145, d240386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211146 q = 1) : d240387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211146, d240387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211146, d240387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58793 (p : Pattern) (ha : d208034 p = 1) (hb : d211152 p = 1) : d240393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23206 q = 1) (hb : d208034 q = 1) : d240283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23206, d240283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23206, d240283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58771 q ha hb
  have h2 (q : Pattern) (ha : d23207 q = 1) (hb : d208034 q = 1) : d240284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23207, d240284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23207, d240284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23213 q = 1) (hb : d208034 q = 1) : d240290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58771 q ha hb
    | true =>
      simp only [d23213, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58772 q ha hb
  have h4 (q : Pattern) (ha : d23214 q = 1) (hb : d208034 q = 1) : d240291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23214, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23215 q = 1) (hb : d208034 q = 1) : d240292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23215, d240292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23215, d240292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211130 q = 1) : d240349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211130, d240349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58781 q ha hb
    | true =>
      simp only [d211130, d240349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58786 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d208034 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23298 q = 1) (hb : d208034 q = 1) : d240351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23298, d240351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58773 q ha hb
    | true =>
      simp only [d23298, d240351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211131 q = 1) : d240352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211131, d240352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211131, d240352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211132 q = 1) : d240353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211132, d240353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211132, d240353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211133 q = 1) : d240354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211133, d240354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211133, d240354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211137 q = 1) : d240358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211137, d240358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211137, d240358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58787 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d208034 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211138 q = 1) : d240359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211138, d240359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211138, d240359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211139 q = 1) : d240360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211139, d240360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211139, d240360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211140 q = 1) : d240361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211140, d240361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211140, d240361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211141 q = 1) : d240362 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211141, d240362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211141, d240362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208034 q = 1) (hb : d211147 q = 1) : d240388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211147, d240388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211147, d240388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58792 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d208034 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d208034 q = 1) (hb : d211148 q = 1) : d240389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211148, d240389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d211148, d240389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d208034 q = 1) (hb : d211149 q = 1) : d240390 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211149, d240390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211149, d240390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208034 q = 1) (hb : d211150 q = 1) : d240391 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211150, d240391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211150, d240391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211151 q = 1) : d240392 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211151, d240392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d211151, d240392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d208034 q = 1) (hb : d211152 q = 1) : d240393 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211152, d240393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211152, d240393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro58794 (p : Pattern) (ha : d208034 p = 1) (hb : d211158 p = 1) : d240399 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d208034 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211115 q = 1) : d240273 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211115, d240273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211115, d240273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58770 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211116 q = 1) : d240274 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211116, d240274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211116, d240274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d211117 q = 1) : d240275 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211117, d240275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211117, d240275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211118 q = 1) : d240276 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211118, d240276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211118, d240276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211119 q = 1) : d240277 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211119, d240277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211119, d240277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211153 q = 1) : d240394 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211153, d240394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211153, d240394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58793 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211154 q = 1) : d240395 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211154, d240395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211154, d240395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211155 q = 1) : d240396 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211155, d240396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211155, d240396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211156 q = 1) : d240397 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211156, d240397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211156, d240397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211157 q = 1) : d240398 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211157, d240398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211157, d240398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211158 q = 1) : d240399 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211158, d240399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211158, d240399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58795 (p : Pattern) (ha : d23368 p = 1) (hb : d208034 p = 1) : d240402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23237 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58777 q ha hb
    | true =>
      simp only [d23237, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
  have h2 (q : Pattern) (ha : d23238 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23239 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23135 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
    | true =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23136 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23137 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23240 q = 1) (hb : d208034 q = 1) : d240309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23240, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23366 q = 1) (hb : d208034 q = 1) : d240400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23366, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23366, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23367 q = 1) (hb : d208034 q = 1) : d240401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23367, d240401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23367, d240401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23368 q = 1) (hb : d208034 q = 1) : d240402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23368, d240402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23368, d240402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro58796 (p : Pattern) (ha : d23372 p = 1) (hb : d208034 p = 1) : d240406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23135 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
    | true =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23136 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23137 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23366 q = 1) (hb : d208034 q = 1) : d240400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23366, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23366, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23371 q = 1) (hb : d208034 q = 1) : d240405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23371, d240405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23371, d240405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23372 q = 1) (hb : d208034 q = 1) : d240406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23372, d240406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23372, d240406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro58797 (p : Pattern) (ha : d23378 p = 1) (hb : d208034 p = 1) : d240412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23377 q = 1) (hb : d208034 q = 1) : d240411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23377, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23377, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23378 q = 1) (hb : d208034 q = 1) : d240412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23378, d240412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23378, d240412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58798 (p : Pattern) (ha : d23382 p = 1) (hb : d208034 p = 1) : d240416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23381 q = 1) (hb : d208034 q = 1) : d240415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23381, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23381, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23382 q = 1) (hb : d208034 q = 1) : d240416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23382, d240416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23382, d240416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58799 (p : Pattern) (ha : d23388 p = 1) (hb : d208034 p = 1) : d240422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d208034 q = 1) : d240417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58797 q ha hb
    | true =>
      simp only [d23383, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58798 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d208034 q = 1) : d240418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d208034 q = 1) : d240419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d208034 q = 1) : d240420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d208034 q = 1) : d240421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23388 q = 1) (hb : d208034 q = 1) : d240422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58800 (p : Pattern) (ha : d23391 p = 1) (hb : d208034 p = 1) : d240425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23377 q = 1) (hb : d208034 q = 1) : d240411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23377, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23377, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23391 q = 1) (hb : d208034 q = 1) : d240425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23391, d240425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23391, d240425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58801 (p : Pattern) (ha : d23392 p = 1) (hb : d208034 p = 1) : d240426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23381 q = 1) (hb : d208034 q = 1) : d240415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23381, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23381, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23392 q = 1) (hb : d208034 q = 1) : d240426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23392, d240426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23392, d240426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58802 (p : Pattern) (ha : d23398 p = 1) (hb : d208034 p = 1) : d240432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d208034 q = 1) : d240417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58797 q ha hb
    | true =>
      simp only [d23383, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58798 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d208034 q = 1) : d240418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d208034 q = 1) : d240419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d208034 q = 1) : d240420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d208034 q = 1) : d240421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23393 q = 1) (hb : d208034 q = 1) : d240427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58800 q ha hb
    | true =>
      simp only [d23393, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58801 q ha hb
  have h7 (q : Pattern) (ha : d23394 q = 1) (hb : d208034 q = 1) : d240428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23394, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23395 q = 1) (hb : d208034 q = 1) : d240429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23395, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23396 q = 1) (hb : d208034 q = 1) : d240430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23397 q = 1) (hb : d208034 q = 1) : d240431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23398 q = 1) (hb : d208034 q = 1) : d240432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23398, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58803 (p : Pattern) (ha : d23513 p = 1) (hb : d208034 p = 1) : d240505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d208034 q = 1) : d240417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58797 q ha hb
    | true =>
      simp only [d23383, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58798 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d208034 q = 1) : d240418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d208034 q = 1) : d240419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d208034 q = 1) : d240420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d208034 q = 1) : d240421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23508 q = 1) (hb : d208034 q = 1) : d240500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23508, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58798 q ha hb
    | true =>
      simp only [d23508, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23509 q = 1) (hb : d208034 q = 1) : d240501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23509, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23509, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23510 q = 1) (hb : d208034 q = 1) : d240502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23510, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23510, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23511 q = 1) (hb : d208034 q = 1) : d240503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23511, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23511, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23512 q = 1) (hb : d208034 q = 1) : d240504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23512, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23512, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23513 q = 1) (hb : d208034 q = 1) : d240505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23513, d240505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23513, d240505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58804 (p : Pattern) (ha : d23519 p = 1) (hb : d208034 p = 1) : d240511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23508 q = 1) (hb : d208034 q = 1) : d240500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23508, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58798 q ha hb
    | true =>
      simp only [d23508, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23509 q = 1) (hb : d208034 q = 1) : d240501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23509, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23509, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23510 q = 1) (hb : d208034 q = 1) : d240502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23510, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23510, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23511 q = 1) (hb : d208034 q = 1) : d240503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23511, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23511, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23512 q = 1) (hb : d208034 q = 1) : d240504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23512, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23512, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23514 q = 1) (hb : d208034 q = 1) : d240506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23514, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58801 q ha hb
    | true =>
      simp only [d23514, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23515 q = 1) (hb : d208034 q = 1) : d240507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23515, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23515, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23516 q = 1) (hb : d208034 q = 1) : d240508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23516, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23516, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23517 q = 1) (hb : d208034 q = 1) : d240509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23517, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23517, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23518 q = 1) (hb : d208034 q = 1) : d240510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23518, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23518, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23519 q = 1) (hb : d208034 q = 1) : d240511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23519, d240511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23519, d240511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58805 (p : Pattern) (ha : d23528 p = 1) (hb : d208034 p = 1) : d240520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23514 q = 1) (hb : d208034 q = 1) : d240506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23514, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58801 q ha hb
    | true =>
      simp only [d23514, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23515 q = 1) (hb : d208034 q = 1) : d240507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23515, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23515, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23516 q = 1) (hb : d208034 q = 1) : d240508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23516, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23516, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23517 q = 1) (hb : d208034 q = 1) : d240509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23517, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23517, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23518 q = 1) (hb : d208034 q = 1) : d240510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23518, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23518, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23528 q = 1) (hb : d208034 q = 1) : d240520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23528, d240520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23528, d240520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58806 (p : Pattern) (ha : d23558 p = 1) (hb : d208034 p = 1) : d240545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23172 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
    | true =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23173 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23174 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23548 q = 1) (hb : d208034 q = 1) : d240535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23548, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23548, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23557 q = 1) (hb : d208034 q = 1) : d240544 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23557, d240544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23557, d240544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23558 q = 1) (hb : d208034 q = 1) : d240545 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23558, d240545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23558, d240545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro58807 (p : Pattern) (ha : d23609 p = 1) (hb : d208034 p = 1) : d240568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23559 q = 1) (hb : d208034 q = 1) : d240546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23559, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58806 q ha hb
    | true =>
      simp only [d23559, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23560 q = 1) (hb : d208034 q = 1) : d240547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23560, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23560, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23606 q = 1) (hb : d208034 q = 1) : d240565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23606, d240565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23606, d240565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23607 q = 1) (hb : d208034 q = 1) : d240566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23607, d240566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23607, d240566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23608 q = 1) (hb : d208034 q = 1) : d240567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23608, d240567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23608, d240567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23609 q = 1) (hb : d208034 q = 1) : d240568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23609, d240568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23609, d240568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58808 (p : Pattern) (ha : d23615 p = 1) (hb : d208034 p = 1) : d240574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23610 q = 1) (hb : d208034 q = 1) : d240569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23610, d240569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58807 q ha hb
    | true =>
      simp only [d23610, d240569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23611 q = 1) (hb : d208034 q = 1) : d240570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23611, d240570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23611, d240570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23612 q = 1) (hb : d208034 q = 1) : d240571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23612, d240571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23612, d240571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23613 q = 1) (hb : d208034 q = 1) : d240572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23613, d240572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23613, d240572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23614 q = 1) (hb : d208034 q = 1) : d240573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23614, d240573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23614, d240573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23615 q = 1) (hb : d208034 q = 1) : d240574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23615, d240574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23615, d240574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58809 (p : Pattern) (ha : d23403 p = 1) (hb : d208034 p = 1) : d240437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23402 q = 1) (hb : d208034 q = 1) : d240436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23402, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23402, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23403 q = 1) (hb : d208034 q = 1) : d240437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23403, d240437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23403, d240437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58810 (p : Pattern) (ha : d23405 p = 1) (hb : d208034 p = 1) : d240439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23404 q = 1) (hb : d208034 q = 1) : d240438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23404, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23404, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23405 q = 1) (hb : d208034 q = 1) : d240439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23405, d240439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23405, d240439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58811 (p : Pattern) (ha : d23412 p = 1) (hb : d208034 p = 1) : d240446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23410 q = 1) (hb : d208034 q = 1) : d240444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23410, d240444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23410, d240444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23411 q = 1) (hb : d208034 q = 1) : d240445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23411, d240445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23411, d240445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23412 q = 1) (hb : d208034 q = 1) : d240446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23412, d240446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23412, d240446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58812 (p : Pattern) (ha : d23415 p = 1) (hb : d208034 p = 1) : d240449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23413 q = 1) (hb : d208034 q = 1) : d240447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23413, d240447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23413, d240447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23414 q = 1) (hb : d208034 q = 1) : d240448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23414, d240448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23414, d240448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23415 q = 1) (hb : d208034 q = 1) : d240449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23415, d240449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23415, d240449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58813 (p : Pattern) (ha : d23421 p = 1) (hb : d208034 p = 1) : d25783 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d533 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23419 q = 1) (hb : d208034 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23419, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23420 q = 1) (hb : d208034 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d315 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23228 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23228, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23229 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23421 q = 1) (hb : d208034 q = 1) : d25783 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23421, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58814 (p : Pattern) (ha : d23427 p = 1) (hb : d208034 p = 1) : d240453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d208034 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d208034 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23233 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23234 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23426 q = 1) (hb : d208034 q = 1) : d25788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d208034 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d208034 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23235 q = 1) (hb : d208034 q = 1) : d25456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23235, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23427 q = 1) (hb : d208034 q = 1) : d240453 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23427, d240453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23427, d240453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58815 (p : Pattern) (ha : d23433 p = 1) (hb : d208034 p = 1) : d240459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23428 q = 1) (hb : d208034 q = 1) : d240454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23428, d240454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58814 q ha hb
    | true =>
      simp only [d23428, d240454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58777 q ha hb
  have h2 (q : Pattern) (ha : d23429 q = 1) (hb : d208034 q = 1) : d240455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23429, d240455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23429, d240455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23430 q = 1) (hb : d208034 q = 1) : d240456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23430, d240456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23430, d240456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23237 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58777 q ha hb
    | true =>
      simp only [d23237, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
  have h5 (q : Pattern) (ha : d23238 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23239 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23431 q = 1) (hb : d208034 q = 1) : d240457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23431, d240457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23431, d240457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23135 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58759 q ha hb
    | true =>
      simp only [d23135, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23136 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23137 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23240 q = 1) (hb : d208034 q = 1) : d240309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23240, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23432 q = 1) (hb : d208034 q = 1) : d240458 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23432, d240458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23432, d240458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23433 q = 1) (hb : d208034 q = 1) : d240459 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23433, d240459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23433, d240459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro58816 (p : Pattern) (ha : d23439 p = 1) (hb : d208034 p = 1) : d240465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23434 q = 1) (hb : d208034 q = 1) : d240460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23434, d240460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58815 q ha hb
    | true =>
      simp only [d23434, d240460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23435 q = 1) (hb : d208034 q = 1) : d240461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23435, d240461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23435, d240461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23436 q = 1) (hb : d208034 q = 1) : d240462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23436, d240462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23436, d240462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23437 q = 1) (hb : d208034 q = 1) : d240463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23437, d240463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23437, d240463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23438 q = 1) (hb : d208034 q = 1) : d240464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23438, d240464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23438, d240464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23439 q = 1) (hb : d208034 q = 1) : d240465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23439, d240465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23439, d240465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58817 (p : Pattern) (ha : d23476 p = 1) (hb : d208034 p = 1) : d240471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23473 q = 1) (hb : d208034 q = 1) : d240468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23473, d240468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23473, d240468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23474 q = 1) (hb : d208034 q = 1) : d240469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23474, d240469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23474, d240469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23475 q = 1) (hb : d208034 q = 1) : d240470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23475, d240470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23475, d240470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23476 q = 1) (hb : d208034 q = 1) : d240471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23476, d240471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23476, d240471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58818 (p : Pattern) (ha : d208034 p = 1) (hb : d211163 p = 1) : d240477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23406 q = 1) (hb : d208034 q = 1) : d240440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23406, d240440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58809 q ha hb
    | true =>
      simp only [d23406, d240440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58810 q ha hb
  have h2 (q : Pattern) (ha : d23407 q = 1) (hb : d208034 q = 1) : d240441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23407, d240441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23407, d240441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23408 q = 1) (hb : d208034 q = 1) : d240442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23408, d240442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23408, d240442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23409 q = 1) (hb : d208034 q = 1) : d240443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23409, d240443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23409, d240443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23416 q = 1) (hb : d208034 q = 1) : d240450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23416, d240450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58811 q ha hb
    | true =>
      simp only [d23416, d240450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58812 q ha hb
  have h6 (q : Pattern) (ha : d23417 q = 1) (hb : d208034 q = 1) : d240451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23417, d240451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23417, d240451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23418 q = 1) (hb : d208034 q = 1) : d240452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23418, d240452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23418, d240452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23440 q = 1) (hb : d208034 q = 1) : d240466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23440, d240466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58816 q ha hb
    | true =>
      simp only [d23440, d240466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58797 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211159 q = 1) : d240467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d240467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211159, d240467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23477 q = 1) (hb : d208034 q = 1) : d240472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23477, d240472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58817 q ha hb
    | true =>
      simp only [d23477, d240472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23478 q = 1) (hb : d208034 q = 1) : d240473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23478, d240473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23478, d240473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211160 q = 1) : d240474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d240474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211160, d240474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211161 q = 1) : d240475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d240475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211161, d240475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211162 q = 1) : d240476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d240476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211162, d240476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211163 q = 1) : d240477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211163, d240477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211163, d240477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58819 (p : Pattern) (ha : d23483 p = 1) (hb : d208034 p = 1) : d240478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23402 q = 1) (hb : d208034 q = 1) : d240436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23402, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23402, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23483 q = 1) (hb : d208034 q = 1) : d240478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23483, d240478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23483, d240478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58820 (p : Pattern) (ha : d23484 p = 1) (hb : d208034 p = 1) : d240479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23404 q = 1) (hb : d208034 q = 1) : d240438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23404, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23404, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23484 q = 1) (hb : d208034 q = 1) : d240479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23484, d240479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23484, d240479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58821 (p : Pattern) (ha : d23489 p = 1) (hb : d208034 p = 1) : d240484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23410 q = 1) (hb : d208034 q = 1) : d240444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23410, d240444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23410, d240444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23411 q = 1) (hb : d208034 q = 1) : d240445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23411, d240445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23411, d240445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23489 q = 1) (hb : d208034 q = 1) : d240484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23489, d240484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23489, d240484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58822 (p : Pattern) (ha : d23490 p = 1) (hb : d208034 p = 1) : d240485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58796 q ha hb
    | true =>
      simp only [d23373, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23413 q = 1) (hb : d208034 q = 1) : d240447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23413, d240447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23413, d240447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23414 q = 1) (hb : d208034 q = 1) : d240448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23414, d240448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23414, d240448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23490 q = 1) (hb : d208034 q = 1) : d240485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23490, d240485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23490, d240485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58823 (p : Pattern) (ha : d23494 p = 1) (hb : d208034 p = 1) : d240489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23434 q = 1) (hb : d208034 q = 1) : d240460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23434, d240460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58815 q ha hb
    | true =>
      simp only [d23434, d240460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23435 q = 1) (hb : d208034 q = 1) : d240461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23435, d240461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23435, d240461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23436 q = 1) (hb : d208034 q = 1) : d240462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23436, d240462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23436, d240462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23437 q = 1) (hb : d208034 q = 1) : d240463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23437, d240463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23437, d240463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23438 q = 1) (hb : d208034 q = 1) : d240464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23438, d240464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23438, d240464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23494 q = 1) (hb : d208034 q = 1) : d240489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23494, d240489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23494, d240489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58824 (p : Pattern) (ha : d23500 p = 1) (hb : d208034 p = 1) : d240492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58795 q ha hb
    | true =>
      simp only [d23369, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23473 q = 1) (hb : d208034 q = 1) : d240468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23473, d240468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23473, d240468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23474 q = 1) (hb : d208034 q = 1) : d240469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23474, d240469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23474, d240469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23475 q = 1) (hb : d208034 q = 1) : d240470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23475, d240470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23475, d240470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23500 q = 1) (hb : d208034 q = 1) : d240492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23500, d240492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23500, d240492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58825 (p : Pattern) (ha : d208034 p = 1) (hb : d211168 p = 1) : d240498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23406 q = 1) (hb : d208034 q = 1) : d240440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23406, d240440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58809 q ha hb
    | true =>
      simp only [d23406, d240440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58810 q ha hb
  have h2 (q : Pattern) (ha : d23407 q = 1) (hb : d208034 q = 1) : d240441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23407, d240441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23407, d240441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23408 q = 1) (hb : d208034 q = 1) : d240442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23408, d240442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23408, d240442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23409 q = 1) (hb : d208034 q = 1) : d240443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23409, d240443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23409, d240443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23416 q = 1) (hb : d208034 q = 1) : d240450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23416, d240450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58811 q ha hb
    | true =>
      simp only [d23416, d240450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58812 q ha hb
  have h6 (q : Pattern) (ha : d23417 q = 1) (hb : d208034 q = 1) : d240451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23417, d240451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23417, d240451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23418 q = 1) (hb : d208034 q = 1) : d240452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23418, d240452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23418, d240452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23440 q = 1) (hb : d208034 q = 1) : d240466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23440, d240466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58816 q ha hb
    | true =>
      simp only [d23440, d240466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58797 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211159 q = 1) : d240467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d240467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211159, d240467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23477 q = 1) (hb : d208034 q = 1) : d240472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23477, d240472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58817 q ha hb
    | true =>
      simp only [d23477, d240472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23478 q = 1) (hb : d208034 q = 1) : d240473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23478, d240473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23478, d240473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211160 q = 1) : d240474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d240474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211160, d240474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211161 q = 1) : d240475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d240475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211161, d240475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211162 q = 1) : d240476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d240476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211162, d240476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23485 q = 1) (hb : d208034 q = 1) : d240480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23485, d240480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58819 q ha hb
    | true =>
      simp only [d23485, d240480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58820 q ha hb
  have h16 (q : Pattern) (ha : d23486 q = 1) (hb : d208034 q = 1) : d240481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23486, d240481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23486, d240481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23487 q = 1) (hb : d208034 q = 1) : d240482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23487, d240482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23487, d240482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23488 q = 1) (hb : d208034 q = 1) : d240483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23488, d240483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23488, d240483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23491 q = 1) (hb : d208034 q = 1) : d240486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23491, d240486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58821 q ha hb
    | true =>
      simp only [d23491, d240486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58822 q ha hb
  have h20 (q : Pattern) (ha : d23492 q = 1) (hb : d208034 q = 1) : d240487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23492, d240487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23492, d240487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23493 q = 1) (hb : d208034 q = 1) : d240488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23493, d240488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23493, d240488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23495 q = 1) (hb : d208034 q = 1) : d240490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23495, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58823 q ha hb
    | true =>
      simp only [d23495, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58800 q ha hb
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211164 q = 1) : d240491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d211164, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d23501 q = 1) (hb : d208034 q = 1) : d240493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23501, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58824 q ha hb
    | true =>
      simp only [d23501, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d23502 q = 1) (hb : d208034 q = 1) : d240494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23502, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23502, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d208034 q = 1) (hb : d211165 q = 1) : d240495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211165, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d208034 q = 1) (hb : d211166 q = 1) : d240496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211166, d240496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211166, d240496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d208034 q = 1) (hb : d211167 q = 1) : d240497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211167, d240497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d211167, d240497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d208034 q = 1) (hb : d211168 q = 1) : d240498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211168, d240498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211168, d240498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro58826 (p : Pattern) (ha : d208034 p = 1) (hb : d211175 p = 1) : d240518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23495 q = 1) (hb : d208034 q = 1) : d240490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23495, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58823 q ha hb
    | true =>
      simp only [d23495, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58800 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211164 q = 1) : d240491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211164, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23501 q = 1) (hb : d208034 q = 1) : d240493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23501, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58824 q ha hb
    | true =>
      simp only [d23501, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23502 q = 1) (hb : d208034 q = 1) : d240494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23502, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23502, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211165 q = 1) : d240495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211165, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211173 q = 1) : d240516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211173, d240516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211173, d240516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211174 q = 1) : d240517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211174, d240517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211174, d240517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211175 q = 1) : d240518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211175, d240518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211175, d240518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58827 (p : Pattern) (ha : d23539 p = 1) (hb : d208034 p = 1) : d240526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d208034 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d208034 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d208034 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d208034 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23310 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
  have h8 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23311 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23312 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23313 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23538 q = 1) (hb : d208034 q = 1) : d25946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d208034 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58758 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d208034 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d208034 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d208034 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23314 q = 1) (hb : d208034 q = 1) : d25590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23314, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23539 q = 1) (hb : d208034 q = 1) : d240526 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23539, d240526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23539, d240526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58828 (p : Pattern) (ha : d23545 p = 1) (hb : d208034 p = 1) : d240532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23540 q = 1) (hb : d208034 q = 1) : d240527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23540, d240527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58827 q ha hb
    | true =>
      simp only [d23540, d240527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58788 q ha hb
  have h2 (q : Pattern) (ha : d23541 q = 1) (hb : d208034 q = 1) : d240528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23541, d240528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23541, d240528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23542 q = 1) (hb : d208034 q = 1) : d240529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23542, d240529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23542, d240529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23316 q = 1) (hb : d208034 q = 1) : d240364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58788 q ha hb
    | true =>
      simp only [d23316, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
  have h5 (q : Pattern) (ha : d23317 q = 1) (hb : d208034 q = 1) : d240365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23318 q = 1) (hb : d208034 q = 1) : d240366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23543 q = 1) (hb : d208034 q = 1) : d240530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23543, d240530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23543, d240530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23172 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
    | true =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23173 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23174 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23319 q = 1) (hb : d208034 q = 1) : d240367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23319, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23544 q = 1) (hb : d208034 q = 1) : d240531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23544, d240531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23544, d240531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23545 q = 1) (hb : d208034 q = 1) : d240532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23545, d240532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23545, d240532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro58829 (p : Pattern) (ha : d23550 p = 1) (hb : d208034 p = 1) : d240537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23316 q = 1) (hb : d208034 q = 1) : d240364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58788 q ha hb
    | true =>
      simp only [d23316, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
  have h2 (q : Pattern) (ha : d23317 q = 1) (hb : d208034 q = 1) : d240365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23318 q = 1) (hb : d208034 q = 1) : d240366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23172 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58766 q ha hb
    | true =>
      simp only [d23172, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23173 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23174 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23319 q = 1) (hb : d208034 q = 1) : d240367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23319, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23548 q = 1) (hb : d208034 q = 1) : d240535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23548, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23548, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23549 q = 1) (hb : d208034 q = 1) : d240536 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23549, d240536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23549, d240536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23550 q = 1) (hb : d208034 q = 1) : d240537 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23550, d240537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23550, d240537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro58830 (p : Pattern) (ha : d23556 p = 1) (hb : d208034 p = 1) : d240543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23546 q = 1) (hb : d208034 q = 1) : d240533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23546, d240533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58828 q ha hb
    | true =>
      simp only [d23546, d240533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23547 q = 1) (hb : d208034 q = 1) : d240534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23547, d240534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23547, d240534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23551 q = 1) (hb : d208034 q = 1) : d240538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58829 q ha hb
    | true =>
      simp only [d23551, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23552 q = 1) (hb : d208034 q = 1) : d240539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23553 q = 1) (hb : d208034 q = 1) : d240540 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23553, d240540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23553, d240540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23554 q = 1) (hb : d208034 q = 1) : d240541 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23554, d240541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23554, d240541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23555 q = 1) (hb : d208034 q = 1) : d240542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23555, d240542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23555, d240542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23556 q = 1) (hb : d208034 q = 1) : d240543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23556, d240543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23556, d240543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58831 (p : Pattern) (ha : d23564 p = 1) (hb : d208034 p = 1) : d240551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23551 q = 1) (hb : d208034 q = 1) : d240538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58829 q ha hb
    | true =>
      simp only [d23551, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23552 q = 1) (hb : d208034 q = 1) : d240539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23559 q = 1) (hb : d208034 q = 1) : d240546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23559, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58806 q ha hb
    | true =>
      simp only [d23559, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23560 q = 1) (hb : d208034 q = 1) : d240547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23560, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23560, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23561 q = 1) (hb : d208034 q = 1) : d240548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23561, d240548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23561, d240548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23562 q = 1) (hb : d208034 q = 1) : d240549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23562, d240549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23562, d240549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23563 q = 1) (hb : d208034 q = 1) : d240550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23563, d240550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23563, d240550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23564 q = 1) (hb : d208034 q = 1) : d240551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23564, d240551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23564, d240551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58832 (p : Pattern) (ha : d23598 p = 1) (hb : d208034 p = 1) : d240557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23551 q = 1) (hb : d208034 q = 1) : d240538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58829 q ha hb
    | true =>
      simp only [d23551, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23552 q = 1) (hb : d208034 q = 1) : d240539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23595 q = 1) (hb : d208034 q = 1) : d240554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23595, d240554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23595, d240554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23596 q = 1) (hb : d208034 q = 1) : d240555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23596, d240555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23596, d240555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23597 q = 1) (hb : d208034 q = 1) : d240556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23597, d240556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23597, d240556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23598 q = 1) (hb : d208034 q = 1) : d240557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23598, d240557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23598, d240557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58833 (p : Pattern) (ha : d208034 p = 1) (hb : d211185 p = 1) : d240563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23565 q = 1) (hb : d208034 q = 1) : d240552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23565, d240552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58830 q ha hb
    | true =>
      simp only [d23565, d240552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58831 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211181 q = 1) : d240553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211181, d240553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211181, d240553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23599 q = 1) (hb : d208034 q = 1) : d240558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23599, d240558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58832 q ha hb
    | true =>
      simp only [d23599, d240558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23600 q = 1) (hb : d208034 q = 1) : d240559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23600, d240559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23600, d240559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211182 q = 1) : d240560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211182, d240560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211182, d240560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211183 q = 1) : d240561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211183, d240561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211183, d240561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211184 q = 1) : d240562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211184, d240562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211184, d240562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211185 q = 1) : d240563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211185, d240563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211185, d240563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58834 (p : Pattern) (ha : d208034 p = 1) (hb : d211191 p = 1) : d240580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23389 q = 1) (hb : d208034 q = 1) : d240423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23389, d240423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23389, d240423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58799 q ha hb
  have h2 (q : Pattern) (ha : d23390 q = 1) (hb : d208034 q = 1) : d240424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23390, d240424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23390, d240424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23399 q = 1) (hb : d208034 q = 1) : d240433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58799 q ha hb
    | true =>
      simp only [d23399, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58802 q ha hb
  have h4 (q : Pattern) (ha : d23400 q = 1) (hb : d208034 q = 1) : d240434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23400, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23401 q = 1) (hb : d208034 q = 1) : d240435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23401, d240435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23401, d240435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211169 q = 1) : d240499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211169, d240499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58818 q ha hb
    | true =>
      simp only [d211169, d240499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58825 q ha hb
  have h7 (q : Pattern) (ha : d23520 q = 1) (hb : d208034 q = 1) : d240512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23520, d240512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58803 q ha hb
    | true =>
      simp only [d23520, d240512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58804 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211170 q = 1) : d240513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211170, d240513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211170, d240513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211171 q = 1) : d240514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211171, d240514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211171, d240514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211172 q = 1) : d240515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211172, d240515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211172, d240515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211176 q = 1) : d240519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211176, d240519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211176, d240519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58826 q ha hb
  have h12 (q : Pattern) (ha : d23529 q = 1) (hb : d208034 q = 1) : d240521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23529, d240521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23529, d240521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58805 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211177 q = 1) : d240522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211177, d240522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211177, d240522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211178 q = 1) : d240523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211178, d240523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211178, d240523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211179 q = 1) : d240524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211179, d240524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211179, d240524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211180 q = 1) : d240525 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211180, d240525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211180, d240525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211186 q = 1) : d240564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211186, d240564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211186, d240564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58833 q ha hb
  have h18 (q : Pattern) (ha : d23616 q = 1) (hb : d208034 q = 1) : d240575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23616, d240575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23616, d240575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58808 q ha hb
  have h19 (q : Pattern) (ha : d208034 q = 1) (hb : d211187 q = 1) : d240576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211187, d240576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211187, d240576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d208034 q = 1) (hb : d211188 q = 1) : d240577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211188, d240577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211188, d240577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208034 q = 1) (hb : d211189 q = 1) : d240578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211189, d240578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211189, d240578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208034 q = 1) (hb : d211190 q = 1) : d240579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211190, d240579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211190, d240579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211191 q = 1) : d240580 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211191, d240580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211191, d240580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro58835 (p : Pattern) (ha : d208034 p = 1) (hb : d211197 p = 1) : d240586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d211192 q = 1) : d240581 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211192, d240581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211192, d240581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58834 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211193 q = 1) : d240582 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211193, d240582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211193, d240582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211194 q = 1) : d240583 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211194, d240583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211194, d240583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d211195 q = 1) : d240584 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211195, d240584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211195, d240584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211196 q = 1) : d240585 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211196, d240585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211196, d240585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211197 q = 1) : d240586 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211197, d240586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211197, d240586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58836 (p : Pattern) (ha : d5450 p = 1) (hb : d208034 p = 1) : d200353 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5449 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5450 q = 1) (hb : d208034 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5450, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro58837 (p : Pattern) (ha : d5457 p = 1) (hb : d208034 p = 1) : d209923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5455 q = 1) (hb : d208034 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5457 q = 1) (hb : d208034 q = 1) : d209923 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5457, d209923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5457, d209923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58838 (p : Pattern) (ha : d23630 p = 1) (hb : d208034 p = 1) : d240589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d208034 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d208034 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23233 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23234 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23426 q = 1) (hb : d208034 q = 1) : d25788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23629 q = 1) (hb : d208034 q = 1) : d240588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23629, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23629, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23630 q = 1) (hb : d208034 q = 1) : d240589 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23630, d240589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23630, d240589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58839 (p : Pattern) (ha : d23631 p = 1) (hb : d208034 p = 1) : d240590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5451 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5452 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5453 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5454 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23629 q = 1) (hb : d208034 q = 1) : d240588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23629, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23629, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5455 q = 1) (hb : d208034 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23631 q = 1) (hb : d208034 q = 1) : d240590 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23631, d240590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23631, d240590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58840 (p : Pattern) (ha : d23641 p = 1) (hb : d208034 p = 1) : d240600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23632 q = 1) (hb : d208034 q = 1) : d240591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23632, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58838 q ha hb
    | true =>
      simp only [d23632, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58839 q ha hb
  have h2 (q : Pattern) (ha : d23633 q = 1) (hb : d208034 q = 1) : d240592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23633, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23633, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23634 q = 1) (hb : d208034 q = 1) : d240593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23634, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23634, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23635 q = 1) (hb : d208034 q = 1) : d240594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58839 q ha hb
    | true =>
      simp only [d23635, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58837 q ha hb
  have h5 (q : Pattern) (ha : d23636 q = 1) (hb : d208034 q = 1) : d240595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23637 q = 1) (hb : d208034 q = 1) : d240596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23638 q = 1) (hb : d208034 q = 1) : d240597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23638, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23638, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23639 q = 1) (hb : d208034 q = 1) : d240598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23639, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23639, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23640 q = 1) (hb : d208034 q = 1) : d240599 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23640, d240599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23640, d240599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23641 q = 1) (hb : d208034 q = 1) : d240600 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23641, d240600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23641, d240600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58841 (p : Pattern) (ha : d23645 p = 1) (hb : d208034 p = 1) : d240604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23635 q = 1) (hb : d208034 q = 1) : d240594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58839 q ha hb
    | true =>
      simp only [d23635, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58837 q ha hb
  have h2 (q : Pattern) (ha : d23636 q = 1) (hb : d208034 q = 1) : d240595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23637 q = 1) (hb : d208034 q = 1) : d240596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23639 q = 1) (hb : d208034 q = 1) : d240598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23639, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23639, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23644 q = 1) (hb : d208034 q = 1) : d240603 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23644, d240603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23644, d240603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23645 q = 1) (hb : d208034 q = 1) : d240604 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23645, d240604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23645, d240604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58842 (p : Pattern) (ha : d23651 p = 1) (hb : d208034 p = 1) : d240610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23650 q = 1) (hb : d208034 q = 1) : d240609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23650, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23650, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23651 q = 1) (hb : d208034 q = 1) : d240610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23651, d240610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23651, d240610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58843 (p : Pattern) (ha : d23655 p = 1) (hb : d208034 p = 1) : d240614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23654 q = 1) (hb : d208034 q = 1) : d240613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23654, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23654, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23655 q = 1) (hb : d208034 q = 1) : d240614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23655, d240614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23655, d240614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58844 (p : Pattern) (ha : d23661 p = 1) (hb : d208034 p = 1) : d240620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d208034 q = 1) : d240615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58842 q ha hb
    | true =>
      simp only [d23656, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58843 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d208034 q = 1) : d240616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d208034 q = 1) : d240617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d208034 q = 1) : d240618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d208034 q = 1) : d240619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23661 q = 1) (hb : d208034 q = 1) : d240620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58845 (p : Pattern) (ha : d23664 p = 1) (hb : d208034 p = 1) : d240623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23650 q = 1) (hb : d208034 q = 1) : d240609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23650, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23650, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23664 q = 1) (hb : d208034 q = 1) : d240623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23664, d240623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23664, d240623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58846 (p : Pattern) (ha : d23665 p = 1) (hb : d208034 p = 1) : d240624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23654 q = 1) (hb : d208034 q = 1) : d240613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23654, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23654, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23665 q = 1) (hb : d208034 q = 1) : d240624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23665, d240624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23665, d240624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58847 (p : Pattern) (ha : d23671 p = 1) (hb : d208034 p = 1) : d240630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d208034 q = 1) : d240615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58842 q ha hb
    | true =>
      simp only [d23656, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58843 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d208034 q = 1) : d240616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d208034 q = 1) : d240617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d208034 q = 1) : d240618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d208034 q = 1) : d240619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23666 q = 1) (hb : d208034 q = 1) : d240625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58845 q ha hb
    | true =>
      simp only [d23666, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58846 q ha hb
  have h7 (q : Pattern) (ha : d23667 q = 1) (hb : d208034 q = 1) : d240626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23667, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23668 q = 1) (hb : d208034 q = 1) : d240627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23668, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23669 q = 1) (hb : d208034 q = 1) : d240628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23670 q = 1) (hb : d208034 q = 1) : d240629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23671 q = 1) (hb : d208034 q = 1) : d240630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23671, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58848 (p : Pattern) (ha : d23793 p = 1) (hb : d208034 p = 1) : d240709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d208034 q = 1) : d240615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58842 q ha hb
    | true =>
      simp only [d23656, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58843 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d208034 q = 1) : d240616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d208034 q = 1) : d240617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d208034 q = 1) : d240618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d208034 q = 1) : d240619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23788 q = 1) (hb : d208034 q = 1) : d240704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23788, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58843 q ha hb
    | true =>
      simp only [d23788, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23789 q = 1) (hb : d208034 q = 1) : d240705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23789, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23789, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23790 q = 1) (hb : d208034 q = 1) : d240706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23790, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23790, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23791 q = 1) (hb : d208034 q = 1) : d240707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23791, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23791, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23792 q = 1) (hb : d208034 q = 1) : d240708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23792, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23792, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23793 q = 1) (hb : d208034 q = 1) : d240709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23793, d240709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23793, d240709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58849 (p : Pattern) (ha : d23799 p = 1) (hb : d208034 p = 1) : d240715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23788 q = 1) (hb : d208034 q = 1) : d240704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23788, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58843 q ha hb
    | true =>
      simp only [d23788, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23789 q = 1) (hb : d208034 q = 1) : d240705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23789, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23789, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23790 q = 1) (hb : d208034 q = 1) : d240706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23790, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23790, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23791 q = 1) (hb : d208034 q = 1) : d240707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23791, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23791, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23792 q = 1) (hb : d208034 q = 1) : d240708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23792, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23792, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23794 q = 1) (hb : d208034 q = 1) : d240710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23794, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58846 q ha hb
    | true =>
      simp only [d23794, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23795 q = 1) (hb : d208034 q = 1) : d240711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23795, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23795, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23796 q = 1) (hb : d208034 q = 1) : d240712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23796, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23796, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23797 q = 1) (hb : d208034 q = 1) : d240713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23797, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23797, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23798 q = 1) (hb : d208034 q = 1) : d240714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23798, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23798, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23799 q = 1) (hb : d208034 q = 1) : d240715 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23799, d240715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23799, d240715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58850 (p : Pattern) (ha : d23808 p = 1) (hb : d208034 p = 1) : d240724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23794 q = 1) (hb : d208034 q = 1) : d240710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23794, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58846 q ha hb
    | true =>
      simp only [d23794, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23795 q = 1) (hb : d208034 q = 1) : d240711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23795, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23795, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23796 q = 1) (hb : d208034 q = 1) : d240712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23796, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23796, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23797 q = 1) (hb : d208034 q = 1) : d240713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23797, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23797, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23798 q = 1) (hb : d208034 q = 1) : d240714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23798, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23798, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23808 q = 1) (hb : d208034 q = 1) : d240724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23808, d240724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23808, d240724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58851 (p : Pattern) (ha : d5501 p = 1) (hb : d208034 p = 1) : d210066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5499 q = 1) (hb : d208034 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5501 q = 1) (hb : d208034 q = 1) : d210066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5501, d210066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5501, d210066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58852 (p : Pattern) (ha : d23825 p = 1) (hb : d208034 p = 1) : d240741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5495 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
  have h8 (q : Pattern) (ha : d5451 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5496 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5452 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5497 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5498 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23820 q = 1) (hb : d208034 q = 1) : d240736 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23820, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23820, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5499 q = 1) (hb : d208034 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23825 q = 1) (hb : d208034 q = 1) : d240741 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23825, d240741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23825, d240741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58853 (p : Pattern) (ha : d23848 p = 1) (hb : d208034 p = 1) : d240764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23830 q = 1) (hb : d208034 q = 1) : d240746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58852 q ha hb
    | true =>
      simp only [d23830, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58851 q ha hb
  have h2 (q : Pattern) (ha : d23831 q = 1) (hb : d208034 q = 1) : d240747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23832 q = 1) (hb : d208034 q = 1) : d240748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23838 q = 1) (hb : d208034 q = 1) : d240754 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23838, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23838, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23847 q = 1) (hb : d208034 q = 1) : d240763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23847, d240763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23847, d240763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23848 q = 1) (hb : d208034 q = 1) : d240764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23848, d240764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23848, d240764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58854 (p : Pattern) (ha : d23906 p = 1) (hb : d208034 p = 1) : d240787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23849 q = 1) (hb : d208034 q = 1) : d240765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23849, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58853 q ha hb
    | true =>
      simp only [d23849, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23850 q = 1) (hb : d208034 q = 1) : d240766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23850, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23850, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23903 q = 1) (hb : d208034 q = 1) : d240784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23903, d240784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23903, d240784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23904 q = 1) (hb : d208034 q = 1) : d240785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23904, d240785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23904, d240785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23905 q = 1) (hb : d208034 q = 1) : d240786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23905, d240786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23905, d240786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23906 q = 1) (hb : d208034 q = 1) : d240787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23906, d240787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23906, d240787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58855 (p : Pattern) (ha : d23912 p = 1) (hb : d208034 p = 1) : d240793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23907 q = 1) (hb : d208034 q = 1) : d240788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23907, d240788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58854 q ha hb
    | true =>
      simp only [d23907, d240788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23908 q = 1) (hb : d208034 q = 1) : d240789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23908, d240789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23908, d240789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23909 q = 1) (hb : d208034 q = 1) : d240790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23909, d240790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23909, d240790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23910 q = 1) (hb : d208034 q = 1) : d240791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23910, d240791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23910, d240791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23911 q = 1) (hb : d208034 q = 1) : d240792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23911, d240792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23911, d240792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23912 q = 1) (hb : d208034 q = 1) : d240793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23912, d240793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23912, d240793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58856 (p : Pattern) (ha : d23676 p = 1) (hb : d208034 p = 1) : d240635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23675 q = 1) (hb : d208034 q = 1) : d240634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23675, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23675, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23676 q = 1) (hb : d208034 q = 1) : d240635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23676, d240635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23676, d240635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58857 (p : Pattern) (ha : d23678 p = 1) (hb : d208034 p = 1) : d240637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23677 q = 1) (hb : d208034 q = 1) : d240636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23677, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23677, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23678 q = 1) (hb : d208034 q = 1) : d240637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23678, d240637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23678, d240637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58858 (p : Pattern) (ha : d23685 p = 1) (hb : d208034 p = 1) : d240644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23683 q = 1) (hb : d208034 q = 1) : d240642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23683, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23683, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23684 q = 1) (hb : d208034 q = 1) : d240643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23684, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23684, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23685 q = 1) (hb : d208034 q = 1) : d240644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23685, d240644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23685, d240644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58859 (p : Pattern) (ha : d23688 p = 1) (hb : d208034 p = 1) : d240647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23686 q = 1) (hb : d208034 q = 1) : d240645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23686, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23686, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23687 q = 1) (hb : d208034 q = 1) : d240646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23687, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23687, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23688 q = 1) (hb : d208034 q = 1) : d240647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23688, d240647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23688, d240647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58860 (p : Pattern) (ha : d23694 p = 1) (hb : d208034 p = 1) : d240651 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d824 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d824, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23692 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23692, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23693 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23693, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d533 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23419 q = 1) (hb : d208034 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23419, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23420 q = 1) (hb : d208034 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23694 q = 1) (hb : d208034 q = 1) : d240651 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d240651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23694, d240651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58861 (p : Pattern) (ha : d23700 p = 1) (hb : d208034 p = 1) : d240657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23695 q = 1) (hb : d208034 q = 1) : d240652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58860 q ha hb
    | true =>
      simp only [d23695, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23696 q = 1) (hb : d208034 q = 1) : d240653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23696, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23697 q = 1) (hb : d208034 q = 1) : d240654 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d240654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d240654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23698 q = 1) (hb : d208034 q = 1) : d240655 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d240655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23698, d240655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23422 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23423 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23424 q = 1) (hb : d208034 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23425 q = 1) (hb : d208034 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23699 q = 1) (hb : d208034 q = 1) : d240656 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d240656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23699, d240656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23426 q = 1) (hb : d208034 q = 1) : d25788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23700 q = 1) (hb : d208034 q = 1) : d240657 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23700, d240657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23700, d240657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58862 (p : Pattern) (ha : d23706 p = 1) (hb : d208034 p = 1) : d240663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23701 q = 1) (hb : d208034 q = 1) : d240658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23701, d240658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58861 q ha hb
    | true =>
      simp only [d23701, d240658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58838 q ha hb
  have h2 (q : Pattern) (ha : d23702 q = 1) (hb : d208034 q = 1) : d240659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23702, d240659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23702, d240659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23703 q = 1) (hb : d208034 q = 1) : d240660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23703, d240660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23703, d240660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23632 q = 1) (hb : d208034 q = 1) : d240591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23632, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58838 q ha hb
    | true =>
      simp only [d23632, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58839 q ha hb
  have h5 (q : Pattern) (ha : d23633 q = 1) (hb : d208034 q = 1) : d240592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23633, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23633, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23634 q = 1) (hb : d208034 q = 1) : d240593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23634, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23634, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23704 q = 1) (hb : d208034 q = 1) : d240661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23704, d240661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23704, d240661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23635 q = 1) (hb : d208034 q = 1) : d240594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58839 q ha hb
    | true =>
      simp only [d23635, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58837 q ha hb
  have h9 (q : Pattern) (ha : d23636 q = 1) (hb : d208034 q = 1) : d240595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23637 q = 1) (hb : d208034 q = 1) : d240596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23638 q = 1) (hb : d208034 q = 1) : d240597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23638, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23638, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23705 q = 1) (hb : d208034 q = 1) : d240662 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23705, d240662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23705, d240662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23706 q = 1) (hb : d208034 q = 1) : d240663 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23706, d240663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23706, d240663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58863 (p : Pattern) (ha : d23712 p = 1) (hb : d208034 p = 1) : d240669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23707 q = 1) (hb : d208034 q = 1) : d240664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23707, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58862 q ha hb
    | true =>
      simp only [d23707, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23708 q = 1) (hb : d208034 q = 1) : d240665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23708, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23708, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23709 q = 1) (hb : d208034 q = 1) : d240666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23709, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23709, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23710 q = 1) (hb : d208034 q = 1) : d240667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23710, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23710, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23711 q = 1) (hb : d208034 q = 1) : d240668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23711, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23711, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23712 q = 1) (hb : d208034 q = 1) : d240669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23712, d240669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23712, d240669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58864 (p : Pattern) (ha : d23756 p = 1) (hb : d208034 p = 1) : d240675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23753 q = 1) (hb : d208034 q = 1) : d240672 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23753, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23753, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23754 q = 1) (hb : d208034 q = 1) : d240673 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23754, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23754, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23755 q = 1) (hb : d208034 q = 1) : d240674 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23755, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23755, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23756 q = 1) (hb : d208034 q = 1) : d240675 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23756, d240675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23756, d240675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58865 (p : Pattern) (ha : d208034 p = 1) (hb : d211203 p = 1) : d240681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23679 q = 1) (hb : d208034 q = 1) : d240638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23679, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58856 q ha hb
    | true =>
      simp only [d23679, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58857 q ha hb
  have h2 (q : Pattern) (ha : d23680 q = 1) (hb : d208034 q = 1) : d240639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23680, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23680, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23681 q = 1) (hb : d208034 q = 1) : d240640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23681, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23681, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23682 q = 1) (hb : d208034 q = 1) : d240641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23682, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23682, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23689 q = 1) (hb : d208034 q = 1) : d240648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23689, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58858 q ha hb
    | true =>
      simp only [d23689, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58859 q ha hb
  have h6 (q : Pattern) (ha : d23690 q = 1) (hb : d208034 q = 1) : d240649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23690, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23690, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23691 q = 1) (hb : d208034 q = 1) : d240650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23691, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23691, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23713 q = 1) (hb : d208034 q = 1) : d240670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23713, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58863 q ha hb
    | true =>
      simp only [d23713, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58842 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211199 q = 1) : d240671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211199, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23757 q = 1) (hb : d208034 q = 1) : d240676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23757, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58864 q ha hb
    | true =>
      simp only [d23757, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23758 q = 1) (hb : d208034 q = 1) : d240677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23758, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23758, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211200 q = 1) : d240678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211200, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211201 q = 1) : d240679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211201, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211202 q = 1) : d240680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211202, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211203 q = 1) : d240681 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211203, d240681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211203, d240681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58866 (p : Pattern) (ha : d23763 p = 1) (hb : d208034 p = 1) : d240682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23675 q = 1) (hb : d208034 q = 1) : d240634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23675, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23675, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23763 q = 1) (hb : d208034 q = 1) : d240682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23763, d240682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23763, d240682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58867 (p : Pattern) (ha : d23764 p = 1) (hb : d208034 p = 1) : d240683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23677 q = 1) (hb : d208034 q = 1) : d240636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23677, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23677, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23764 q = 1) (hb : d208034 q = 1) : d240683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23764, d240683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23764, d240683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58868 (p : Pattern) (ha : d23769 p = 1) (hb : d208034 p = 1) : d240688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23683 q = 1) (hb : d208034 q = 1) : d240642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23683, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23683, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23684 q = 1) (hb : d208034 q = 1) : d240643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23684, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23684, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23769 q = 1) (hb : d208034 q = 1) : d240688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23769, d240688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23769, d240688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58869 (p : Pattern) (ha : d23770 p = 1) (hb : d208034 p = 1) : d240689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58841 q ha hb
    | true =>
      simp only [d23646, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23686 q = 1) (hb : d208034 q = 1) : d240645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23686, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23686, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23687 q = 1) (hb : d208034 q = 1) : d240646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23687, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23687, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23770 q = 1) (hb : d208034 q = 1) : d240689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23770, d240689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23770, d240689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58870 (p : Pattern) (ha : d23774 p = 1) (hb : d208034 p = 1) : d240693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23707 q = 1) (hb : d208034 q = 1) : d240664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23707, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58862 q ha hb
    | true =>
      simp only [d23707, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23708 q = 1) (hb : d208034 q = 1) : d240665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23708, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23708, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23709 q = 1) (hb : d208034 q = 1) : d240666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23709, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23709, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23710 q = 1) (hb : d208034 q = 1) : d240667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23710, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23710, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23711 q = 1) (hb : d208034 q = 1) : d240668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23711, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23711, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23774 q = 1) (hb : d208034 q = 1) : d240693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23774, d240693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23774, d240693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58871 (p : Pattern) (ha : d23780 p = 1) (hb : d208034 p = 1) : d240696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58840 q ha hb
    | true =>
      simp only [d23642, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23753 q = 1) (hb : d208034 q = 1) : d240672 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23753, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23753, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23754 q = 1) (hb : d208034 q = 1) : d240673 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23754, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23754, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23755 q = 1) (hb : d208034 q = 1) : d240674 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23755, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23755, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23780 q = 1) (hb : d208034 q = 1) : d240696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23780, d240696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23780, d240696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58872 (p : Pattern) (ha : d208034 p = 1) (hb : d211208 p = 1) : d240702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23679 q = 1) (hb : d208034 q = 1) : d240638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23679, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58856 q ha hb
    | true =>
      simp only [d23679, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58857 q ha hb
  have h2 (q : Pattern) (ha : d23680 q = 1) (hb : d208034 q = 1) : d240639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23680, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23680, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23681 q = 1) (hb : d208034 q = 1) : d240640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23681, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23681, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23682 q = 1) (hb : d208034 q = 1) : d240641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23682, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23682, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23689 q = 1) (hb : d208034 q = 1) : d240648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23689, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58858 q ha hb
    | true =>
      simp only [d23689, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58859 q ha hb
  have h6 (q : Pattern) (ha : d23690 q = 1) (hb : d208034 q = 1) : d240649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23690, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23690, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23691 q = 1) (hb : d208034 q = 1) : d240650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23691, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23691, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23713 q = 1) (hb : d208034 q = 1) : d240670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23713, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58863 q ha hb
    | true =>
      simp only [d23713, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58842 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211199 q = 1) : d240671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211199, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23757 q = 1) (hb : d208034 q = 1) : d240676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23757, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58864 q ha hb
    | true =>
      simp only [d23757, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23758 q = 1) (hb : d208034 q = 1) : d240677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23758, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23758, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211200 q = 1) : d240678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211200, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211201 q = 1) : d240679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211201, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211202 q = 1) : d240680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211202, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23765 q = 1) (hb : d208034 q = 1) : d240684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23765, d240684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58866 q ha hb
    | true =>
      simp only [d23765, d240684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58867 q ha hb
  have h16 (q : Pattern) (ha : d23766 q = 1) (hb : d208034 q = 1) : d240685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23766, d240685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23766, d240685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23767 q = 1) (hb : d208034 q = 1) : d240686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23767, d240686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23767, d240686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23768 q = 1) (hb : d208034 q = 1) : d240687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23768, d240687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23768, d240687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23771 q = 1) (hb : d208034 q = 1) : d240690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23771, d240690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58868 q ha hb
    | true =>
      simp only [d23771, d240690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58869 q ha hb
  have h20 (q : Pattern) (ha : d23772 q = 1) (hb : d208034 q = 1) : d240691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23772, d240691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23772, d240691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23773 q = 1) (hb : d208034 q = 1) : d240692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23773, d240692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23773, d240692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23775 q = 1) (hb : d208034 q = 1) : d240694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23775, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58870 q ha hb
    | true =>
      simp only [d23775, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58845 q ha hb
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211204 q = 1) : d240695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d211204, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d23781 q = 1) (hb : d208034 q = 1) : d240697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23781, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58871 q ha hb
    | true =>
      simp only [d23781, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d23782 q = 1) (hb : d208034 q = 1) : d240698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23782, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23782, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d208034 q = 1) (hb : d211205 q = 1) : d240699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211205, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d208034 q = 1) (hb : d211206 q = 1) : d240700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211206, d240700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211206, d240700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d208034 q = 1) (hb : d211207 q = 1) : d240701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211207, d240701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d211207, d240701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d208034 q = 1) (hb : d211208 q = 1) : d240702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211208, d240702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211208, d240702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro58873 (p : Pattern) (ha : d208034 p = 1) (hb : d211215 p = 1) : d240722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23775 q = 1) (hb : d208034 q = 1) : d240694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23775, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58870 q ha hb
    | true =>
      simp only [d23775, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58845 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211204 q = 1) : d240695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211204, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23781 q = 1) (hb : d208034 q = 1) : d240697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23781, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58871 q ha hb
    | true =>
      simp only [d23781, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23782 q = 1) (hb : d208034 q = 1) : d240698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23782, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23782, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211205 q = 1) : d240699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211205, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211213 q = 1) : d240720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211213, d240720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211213, d240720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211214 q = 1) : d240721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211214, d240721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211214, d240721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211215 q = 1) : d240722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211215, d240722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211215, d240722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58874 (p : Pattern) (ha : d23819 p = 1) (hb : d208034 p = 1) : d240735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23814 q = 1) (hb : d208034 q = 1) : d240730 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23814, d240730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23814, d240730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58860 q ha hb
  have h2 (q : Pattern) (ha : d23695 q = 1) (hb : d208034 q = 1) : d240652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58860 q ha hb
    | true =>
      simp only [d23695, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23815 q = 1) (hb : d208034 q = 1) : d240731 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23815, d240731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23815, d240731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23696 q = 1) (hb : d208034 q = 1) : d240653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23696, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23816 q = 1) (hb : d208034 q = 1) : d240732 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23816, d240732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23816, d240732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23817 q = 1) (hb : d208034 q = 1) : d240733 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23817, d240733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23817, d240733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23534 q = 1) (hb : d208034 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
  have h8 (q : Pattern) (ha : d23422 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23535 q = 1) (hb : d208034 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23423 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23536 q = 1) (hb : d208034 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23537 q = 1) (hb : d208034 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23818 q = 1) (hb : d208034 q = 1) : d240734 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23818, d240734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23818, d240734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23538 q = 1) (hb : d208034 q = 1) : d25946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23819 q = 1) (hb : d208034 q = 1) : d240735 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23819, d240735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23819, d240735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58875 (p : Pattern) (ha : d23821 p = 1) (hb : d208034 p = 1) : d240737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d208034 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58813 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d208034 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d208034 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d208034 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23310 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
  have h8 (q : Pattern) (ha : d23231 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58776 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23311 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23232 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23312 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23313 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23538 q = 1) (hb : d208034 q = 1) : d25946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58836 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23820 q = 1) (hb : d208034 q = 1) : d240736 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23820, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23820, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23821 q = 1) (hb : d208034 q = 1) : d240737 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23821, d240737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23821, d240737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58876 (p : Pattern) (ha : d23835 p = 1) (hb : d208034 p = 1) : d240751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23822 q = 1) (hb : d208034 q = 1) : d240738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23822, d240738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58874 q ha hb
    | true =>
      simp only [d23822, d240738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58875 q ha hb
  have h2 (q : Pattern) (ha : d23823 q = 1) (hb : d208034 q = 1) : d240739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23823, d240739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23823, d240739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23824 q = 1) (hb : d208034 q = 1) : d240740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23824, d240740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23824, d240740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23826 q = 1) (hb : d208034 q = 1) : d240742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23826, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58875 q ha hb
    | true =>
      simp only [d23826, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58852 q ha hb
  have h5 (q : Pattern) (ha : d23827 q = 1) (hb : d208034 q = 1) : d240743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23827, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23827, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23828 q = 1) (hb : d208034 q = 1) : d240744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23828, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23828, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23829 q = 1) (hb : d208034 q = 1) : d240745 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23829, d240745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23829, d240745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23830 q = 1) (hb : d208034 q = 1) : d240746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58852 q ha hb
    | true =>
      simp only [d23830, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58851 q ha hb
  have h9 (q : Pattern) (ha : d23831 q = 1) (hb : d208034 q = 1) : d240747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23832 q = 1) (hb : d208034 q = 1) : d240748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23833 q = 1) (hb : d208034 q = 1) : d240749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23833, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23833, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23834 q = 1) (hb : d208034 q = 1) : d240750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23834, d240750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23834, d240750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23835 q = 1) (hb : d208034 q = 1) : d240751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23835, d240751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23835, d240751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58877 (p : Pattern) (ha : d23840 p = 1) (hb : d208034 p = 1) : d240756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23826 q = 1) (hb : d208034 q = 1) : d240742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23826, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58875 q ha hb
    | true =>
      simp only [d23826, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58852 q ha hb
  have h2 (q : Pattern) (ha : d23827 q = 1) (hb : d208034 q = 1) : d240743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23827, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23827, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23828 q = 1) (hb : d208034 q = 1) : d240744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23828, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23828, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23830 q = 1) (hb : d208034 q = 1) : d240746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58852 q ha hb
    | true =>
      simp only [d23830, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58851 q ha hb
  have h5 (q : Pattern) (ha : d23831 q = 1) (hb : d208034 q = 1) : d240747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23832 q = 1) (hb : d208034 q = 1) : d240748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23833 q = 1) (hb : d208034 q = 1) : d240749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23833, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23833, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23838 q = 1) (hb : d208034 q = 1) : d240754 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23838, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23838, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23839 q = 1) (hb : d208034 q = 1) : d240755 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23839, d240755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23839, d240755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23840 q = 1) (hb : d208034 q = 1) : d240756 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23840, d240756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23840, d240756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58878 (p : Pattern) (ha : d23846 p = 1) (hb : d208034 p = 1) : d240762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23836 q = 1) (hb : d208034 q = 1) : d240752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23836, d240752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58876 q ha hb
    | true =>
      simp only [d23836, d240752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23837 q = 1) (hb : d208034 q = 1) : d240753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23837, d240753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23837, d240753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23841 q = 1) (hb : d208034 q = 1) : d240757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58877 q ha hb
    | true =>
      simp only [d23841, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23842 q = 1) (hb : d208034 q = 1) : d240758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23843 q = 1) (hb : d208034 q = 1) : d240759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23843, d240759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23843, d240759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23844 q = 1) (hb : d208034 q = 1) : d240760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23844, d240760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23844, d240760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23845 q = 1) (hb : d208034 q = 1) : d240761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23845, d240761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23845, d240761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23846 q = 1) (hb : d208034 q = 1) : d240762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23846, d240762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23846, d240762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58879 (p : Pattern) (ha : d23854 p = 1) (hb : d208034 p = 1) : d240770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23841 q = 1) (hb : d208034 q = 1) : d240757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58877 q ha hb
    | true =>
      simp only [d23841, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23842 q = 1) (hb : d208034 q = 1) : d240758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23849 q = 1) (hb : d208034 q = 1) : d240765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23849, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58853 q ha hb
    | true =>
      simp only [d23849, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23850 q = 1) (hb : d208034 q = 1) : d240766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23850, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23850, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23851 q = 1) (hb : d208034 q = 1) : d240767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23851, d240767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23851, d240767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23852 q = 1) (hb : d208034 q = 1) : d240768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23852, d240768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23852, d240768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23853 q = 1) (hb : d208034 q = 1) : d240769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23853, d240769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23853, d240769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23854 q = 1) (hb : d208034 q = 1) : d240770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23854, d240770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23854, d240770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58880 (p : Pattern) (ha : d23895 p = 1) (hb : d208034 p = 1) : d240776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23841 q = 1) (hb : d208034 q = 1) : d240757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58877 q ha hb
    | true =>
      simp only [d23841, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23842 q = 1) (hb : d208034 q = 1) : d240758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23892 q = 1) (hb : d208034 q = 1) : d240773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23892, d240773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23892, d240773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23893 q = 1) (hb : d208034 q = 1) : d240774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23893, d240774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23893, d240774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23894 q = 1) (hb : d208034 q = 1) : d240775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23894, d240775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23894, d240775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23895 q = 1) (hb : d208034 q = 1) : d240776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23895, d240776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23895, d240776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58881 (p : Pattern) (ha : d208034 p = 1) (hb : d211225 p = 1) : d240782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23855 q = 1) (hb : d208034 q = 1) : d240771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23855, d240771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58878 q ha hb
    | true =>
      simp only [d23855, d240771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58879 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211221 q = 1) : d240772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211221, d240772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211221, d240772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23896 q = 1) (hb : d208034 q = 1) : d240777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23896, d240777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58880 q ha hb
    | true =>
      simp only [d23896, d240777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23897 q = 1) (hb : d208034 q = 1) : d240778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23897, d240778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23897, d240778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211222 q = 1) : d240779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211222, d240779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211222, d240779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211223 q = 1) : d240780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211223, d240780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211223, d240780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211224 q = 1) : d240781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211224, d240781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211224, d240781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211225 q = 1) : d240782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211225, d240782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211225, d240782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58882 (p : Pattern) (ha : d208034 p = 1) (hb : d211231 p = 1) : d240799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23662 q = 1) (hb : d208034 q = 1) : d240621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23662, d240621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23662, d240621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58844 q ha hb
  have h2 (q : Pattern) (ha : d23663 q = 1) (hb : d208034 q = 1) : d240622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23663, d240622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23663, d240622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23672 q = 1) (hb : d208034 q = 1) : d240631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58844 q ha hb
    | true =>
      simp only [d23672, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58847 q ha hb
  have h4 (q : Pattern) (ha : d23673 q = 1) (hb : d208034 q = 1) : d240632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23673, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23674 q = 1) (hb : d208034 q = 1) : d240633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23674, d240633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23674, d240633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211209 q = 1) : d240703 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211209, d240703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58865 q ha hb
    | true =>
      simp only [d211209, d240703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58872 q ha hb
  have h7 (q : Pattern) (ha : d23800 q = 1) (hb : d208034 q = 1) : d240716 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23800, d240716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58848 q ha hb
    | true =>
      simp only [d23800, d240716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58849 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211210 q = 1) : d240717 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211210, d240717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211210, d240717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211211 q = 1) : d240718 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211211, d240718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211211, d240718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211212 q = 1) : d240719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211212, d240719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211212, d240719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211216 q = 1) : d240723 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211216, d240723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211216, d240723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58873 q ha hb
  have h12 (q : Pattern) (ha : d23809 q = 1) (hb : d208034 q = 1) : d240725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23809, d240725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23809, d240725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58850 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211217 q = 1) : d240726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211217, d240726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211217, d240726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211218 q = 1) : d240727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211218, d240727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211218, d240727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211219 q = 1) : d240728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211219, d240728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211219, d240728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211220 q = 1) : d240729 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211220, d240729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211220, d240729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211226 q = 1) : d240783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211226, d240783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211226, d240783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58881 q ha hb
  have h18 (q : Pattern) (ha : d23913 q = 1) (hb : d208034 q = 1) : d240794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23913, d240794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23913, d240794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58855 q ha hb
  have h19 (q : Pattern) (ha : d208034 q = 1) (hb : d211227 q = 1) : d240795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211227, d240795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211227, d240795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d208034 q = 1) (hb : d211228 q = 1) : d240796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211228, d240796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211228, d240796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208034 q = 1) (hb : d211229 q = 1) : d240797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211229, d240797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211229, d240797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208034 q = 1) (hb : d211230 q = 1) : d240798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211230, d240798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211230, d240798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211231 q = 1) : d240799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211231, d240799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211231, d240799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro58883 (p : Pattern) (ha : d208034 p = 1) (hb : d211237 p = 1) : d240805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d211232 q = 1) : d240800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211232, d240800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211232, d240800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58882 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211233 q = 1) : d240801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211233, d240801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211233, d240801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211234 q = 1) : d240802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211234, d240802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211234, d240802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d211235 q = 1) : d240803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211235, d240803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211235, d240803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211236 q = 1) : d240804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211236, d240804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211236, d240804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211237 q = 1) : d240805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211237, d240805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211237, d240805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58884 (p : Pattern) (ha : d23931 p = 1) (hb : d208034 p = 1) : d26199 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1090 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23927 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23927, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23927, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23928 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23928, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23928, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1096 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23929 q = 1) (hb : d208034 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23929, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23930 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23930, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23931 q = 1) (hb : d208034 q = 1) : d26199 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23931, d26199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23931, d26199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58885 (p : Pattern) (ha : d23938 p = 1) (hb : d208034 p = 1) : d26100 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1096 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23929 q = 1) (hb : d208034 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23929, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23930 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23930, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1105 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1106 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23936 q = 1) (hb : d208034 q = 1) : d26090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23936, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23937 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23937, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23938 q = 1) (hb : d208034 q = 1) : d26100 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23938, d26100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23938, d26100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58886 (p : Pattern) (ha : d23944 p = 1) (hb : d208034 p = 1) : d240808 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1106 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23936 q = 1) (hb : d208034 q = 1) : d26090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23936, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23937 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23937, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1116 q = 1) : d1116 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1117 q = 1) (hb : d152852 q = 1) : d1132 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d5537 q = 1) (hb : d208034 q = 1) : d1133 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5537, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5537, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d5538 q = 1) (hb : d208034 q = 1) : d1134 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5538, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5538, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23944 q = 1) (hb : d208034 q = 1) : d240808 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23944, d240808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23944, d240808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58887 (p : Pattern) (ha : d23950 p = 1) (hb : d208034 p = 1) : d240814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23932 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58884 q ha hb
    | true =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23933 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23934 q = 1) (hb : d208034 q = 1) : d26202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23934, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23934, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23935 q = 1) (hb : d208034 q = 1) : d26203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23935, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23935, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23941 q = 1) (hb : d208034 q = 1) : d26103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23942 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23943 q = 1) (hb : d208034 q = 1) : d26204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23943, d26204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23943, d26204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23947 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23948 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23949 q = 1) (hb : d208034 q = 1) : d240813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23949, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23950 q = 1) (hb : d208034 q = 1) : d240814 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23950, d240814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23950, d240814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58888 (p : Pattern) (ha : d23952 p = 1) (hb : d208034 p = 1) : d240816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23941 q = 1) (hb : d208034 q = 1) : d26103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23942 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23947 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23948 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23949 q = 1) (hb : d208034 q = 1) : d240813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23949, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23951 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23951, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23952 q = 1) (hb : d208034 q = 1) : d240816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23952, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23952, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58889 (p : Pattern) (ha : d23956 p = 1) (hb : d208034 p = 1) : d240820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23947 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23948 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23951 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23951, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1140 q = 1) (hb : d208034 q = 1) : d1140 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23956 q = 1) (hb : d208034 q = 1) : d240820 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23956, d240820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23956, d240820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58890 (p : Pattern) (ha : d23963 p = 1) (hb : d208034 p = 1) : d240827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23953 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58887 q ha hb
    | true =>
      simp only [d23953, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
  have h2 (q : Pattern) (ha : d23954 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23955 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23957 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
    | true =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58889 q ha hb
  have h5 (q : Pattern) (ha : d23958 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23959 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23960 q = 1) (hb : d208034 q = 1) : d240824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23960, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23961 q = 1) (hb : d208034 q = 1) : d240825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23961, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23962 q = 1) (hb : d208034 q = 1) : d240826 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23962, d240826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23962, d240826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23963 q = 1) (hb : d208034 q = 1) : d240827 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23963, d240827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23963, d240827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58891 (p : Pattern) (ha : d23967 p = 1) (hb : d208034 p = 1) : d240831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23957 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
    | true =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58889 q ha hb
  have h2 (q : Pattern) (ha : d23958 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23959 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23961 q = 1) (hb : d208034 q = 1) : d240825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23961, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23966 q = 1) (hb : d208034 q = 1) : d240830 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23966, d240830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23966, d240830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23967 q = 1) (hb : d208034 q = 1) : d240831 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23967, d240831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23967, d240831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58892 (p : Pattern) (ha : d23973 p = 1) (hb : d208034 p = 1) : d240837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d208034 q = 1) : d240836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23973 q = 1) (hb : d208034 q = 1) : d240837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23973, d240837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23973, d240837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58893 (p : Pattern) (ha : d23977 p = 1) (hb : d208034 p = 1) : d240841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d208034 q = 1) : d240840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23977 q = 1) (hb : d208034 q = 1) : d240841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23977, d240841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23977, d240841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58894 (p : Pattern) (ha : d23983 p = 1) (hb : d208034 p = 1) : d240847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d208034 q = 1) : d240842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58892 q ha hb
    | true =>
      simp only [d23978, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58893 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d208034 q = 1) : d240843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d208034 q = 1) : d240844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d208034 q = 1) : d240845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d208034 q = 1) : d240846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23983 q = 1) (hb : d208034 q = 1) : d240847 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58895 (p : Pattern) (ha : d23986 p = 1) (hb : d208034 p = 1) : d240850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d208034 q = 1) : d240836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23986 q = 1) (hb : d208034 q = 1) : d240850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23986, d240850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23986, d240850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58896 (p : Pattern) (ha : d23987 p = 1) (hb : d208034 p = 1) : d240851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d208034 q = 1) : d240840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23987 q = 1) (hb : d208034 q = 1) : d240851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23987, d240851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23987, d240851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58897 (p : Pattern) (ha : d23993 p = 1) (hb : d208034 p = 1) : d240857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d208034 q = 1) : d240842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58892 q ha hb
    | true =>
      simp only [d23978, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58893 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d208034 q = 1) : d240843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d208034 q = 1) : d240844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d208034 q = 1) : d240845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d208034 q = 1) : d240846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23988 q = 1) (hb : d208034 q = 1) : d240852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58895 q ha hb
    | true =>
      simp only [d23988, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58896 q ha hb
  have h7 (q : Pattern) (ha : d23989 q = 1) (hb : d208034 q = 1) : d240853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23989, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23990 q = 1) (hb : d208034 q = 1) : d240854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23990, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23991 q = 1) (hb : d208034 q = 1) : d240855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23992 q = 1) (hb : d208034 q = 1) : d240856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23993 q = 1) (hb : d208034 q = 1) : d240857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23993, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58898 (p : Pattern) (ha : d24140 p = 1) (hb : d208034 p = 1) : d240945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d208034 q = 1) : d240842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58892 q ha hb
    | true =>
      simp only [d23978, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58893 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d208034 q = 1) : d240843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d208034 q = 1) : d240844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d208034 q = 1) : d240845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d208034 q = 1) : d240846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24135 q = 1) (hb : d208034 q = 1) : d240940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24135, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58893 q ha hb
    | true =>
      simp only [d24135, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24136 q = 1) (hb : d208034 q = 1) : d240941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24136, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24136, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24137 q = 1) (hb : d208034 q = 1) : d240942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24137, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24137, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24138 q = 1) (hb : d208034 q = 1) : d240943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24138, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24138, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24139 q = 1) (hb : d208034 q = 1) : d240944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24139, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24139, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24140 q = 1) (hb : d208034 q = 1) : d240945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24140, d240945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24140, d240945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58899 (p : Pattern) (ha : d24146 p = 1) (hb : d208034 p = 1) : d240951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24135 q = 1) (hb : d208034 q = 1) : d240940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24135, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58893 q ha hb
    | true =>
      simp only [d24135, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24136 q = 1) (hb : d208034 q = 1) : d240941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24136, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24136, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24137 q = 1) (hb : d208034 q = 1) : d240942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24137, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24137, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24138 q = 1) (hb : d208034 q = 1) : d240943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24138, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24138, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24139 q = 1) (hb : d208034 q = 1) : d240944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24139, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24139, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24141 q = 1) (hb : d208034 q = 1) : d240946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24141, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58896 q ha hb
    | true =>
      simp only [d24141, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24142 q = 1) (hb : d208034 q = 1) : d240947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24142, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24142, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24143 q = 1) (hb : d208034 q = 1) : d240948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24143, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24143, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24144 q = 1) (hb : d208034 q = 1) : d240949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24144, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24144, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24145 q = 1) (hb : d208034 q = 1) : d240950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24145, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24145, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24146 q = 1) (hb : d208034 q = 1) : d240951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24146, d240951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24146, d240951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58900 (p : Pattern) (ha : d24155 p = 1) (hb : d208034 p = 1) : d240960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24141 q = 1) (hb : d208034 q = 1) : d240946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24141, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58896 q ha hb
    | true =>
      simp only [d24141, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24142 q = 1) (hb : d208034 q = 1) : d240947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24142, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24142, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24143 q = 1) (hb : d208034 q = 1) : d240948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24143, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24143, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24144 q = 1) (hb : d208034 q = 1) : d240949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24144, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24144, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24145 q = 1) (hb : d208034 q = 1) : d240950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24145, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24145, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24155 q = 1) (hb : d208034 q = 1) : d240960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24155, d240960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24155, d240960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58901 (p : Pattern) (ha : d24186 p = 1) (hb : d208034 p = 1) : d240982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24170 q = 1) (hb : d208034 q = 1) : d26386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
  have h2 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24171 q = 1) (hb : d208034 q = 1) : d26387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24172 q = 1) (hb : d208034 q = 1) : d26388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24173 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24176 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
  have h8 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24177 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24178 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24179 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24180 q = 1) (hb : d208034 q = 1) : d240976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24180, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24180, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24185 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24185, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24185, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24186 q = 1) (hb : d208034 q = 1) : d240982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24186, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24186, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58902 (p : Pattern) (ha : d24191 p = 1) (hb : d208034 p = 1) : d240987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24176 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
  have h2 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24177 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24178 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24179 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24185 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24185, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24185, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1410 q = 1) (hb : d208034 q = 1) : d1410 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d24191 q = 1) (hb : d208034 q = 1) : d240987 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24191, d240987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24191, d240987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro58903 (p : Pattern) (ha : d24210 p = 1) (hb : d208034 p = 1) : d241006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24192 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
    | true =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58902 q ha hb
  have h2 (q : Pattern) (ha : d24193 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24194 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24200 q = 1) (hb : d208034 q = 1) : d240996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24200, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24200, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24209 q = 1) (hb : d208034 q = 1) : d241005 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24209, d241005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24209, d241005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24210 q = 1) (hb : d208034 q = 1) : d241006 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24210, d241006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24210, d241006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58904 (p : Pattern) (ha : d24285 p = 1) (hb : d208034 p = 1) : d241038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24211 q = 1) (hb : d208034 q = 1) : d241007 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24211, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58903 q ha hb
    | true =>
      simp only [d24211, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24212 q = 1) (hb : d208034 q = 1) : d241008 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24212, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24212, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24282 q = 1) (hb : d208034 q = 1) : d241035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24282, d241035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24282, d241035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24283 q = 1) (hb : d208034 q = 1) : d241036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24283, d241036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24283, d241036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24284 q = 1) (hb : d208034 q = 1) : d241037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24284, d241037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24284, d241037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24285 q = 1) (hb : d208034 q = 1) : d241038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24285, d241038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24285, d241038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58905 (p : Pattern) (ha : d24291 p = 1) (hb : d208034 p = 1) : d241044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24286 q = 1) (hb : d208034 q = 1) : d241039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24286, d241039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58904 q ha hb
    | true =>
      simp only [d24286, d241039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24287 q = 1) (hb : d208034 q = 1) : d241040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24287, d241040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24287, d241040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24288 q = 1) (hb : d208034 q = 1) : d241041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24288, d241041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24288, d241041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24289 q = 1) (hb : d208034 q = 1) : d241042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24289, d241042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24289, d241042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24290 q = 1) (hb : d208034 q = 1) : d241043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24290, d241043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24290, d241043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24291 q = 1) (hb : d208034 q = 1) : d241044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24291, d241044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24291, d241044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58906 (p : Pattern) (ha : d23998 p = 1) (hb : d208034 p = 1) : d240862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23997 q = 1) (hb : d208034 q = 1) : d240861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23997, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23997, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23998 q = 1) (hb : d208034 q = 1) : d240862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23998, d240862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23998, d240862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58907 (p : Pattern) (ha : d24000 p = 1) (hb : d208034 p = 1) : d240864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23999 q = 1) (hb : d208034 q = 1) : d240863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23999, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23999, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24000 q = 1) (hb : d208034 q = 1) : d240864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24000, d240864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24000, d240864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58908 (p : Pattern) (ha : d24007 p = 1) (hb : d208034 p = 1) : d240871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24005 q = 1) (hb : d208034 q = 1) : d240869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24005, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24005, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24006 q = 1) (hb : d208034 q = 1) : d240870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24006, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24006, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24007 q = 1) (hb : d208034 q = 1) : d240871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24007, d240871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24007, d240871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58909 (p : Pattern) (ha : d24010 p = 1) (hb : d208034 p = 1) : d240874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24008 q = 1) (hb : d208034 q = 1) : d240872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24008, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24008, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24009 q = 1) (hb : d208034 q = 1) : d240873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24009, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24009, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24010 q = 1) (hb : d208034 q = 1) : d240874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24010, d240874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24010, d240874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58910 (p : Pattern) (ha : d24016 p = 1) (hb : d208034 p = 1) : d240878 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1201 q = 1) : d1201 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1202 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1202, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24014 q = 1) (hb : d208034 q = 1) : d10043 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24014, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24014, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24015 q = 1) (hb : d208034 q = 1) : d10044 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24015, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24015, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1090 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23927 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23927, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23927, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23928 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23928, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23928, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24016 q = 1) (hb : d208034 q = 1) : d240878 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24016, d240878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24016, d240878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58911 (p : Pattern) (ha : d24022 p = 1) (hb : d208034 p = 1) : d240884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24017 q = 1) (hb : d208034 q = 1) : d240879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24017, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58910 q ha hb
    | true =>
      simp only [d24017, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24018 q = 1) (hb : d208034 q = 1) : d240880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24018, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24018, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24019 q = 1) (hb : d208034 q = 1) : d240881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24019, d240881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24019, d240881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24020 q = 1) (hb : d208034 q = 1) : d240882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24020, d240882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24020, d240882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23932 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58884 q ha hb
    | true =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23933 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23934 q = 1) (hb : d208034 q = 1) : d26202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23934, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23934, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23935 q = 1) (hb : d208034 q = 1) : d26203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23935, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23935, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24021 q = 1) (hb : d208034 q = 1) : d240883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24021, d240883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24021, d240883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23941 q = 1) (hb : d208034 q = 1) : d26103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23942 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23943 q = 1) (hb : d208034 q = 1) : d26204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23943, d26204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23943, d26204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24022 q = 1) (hb : d208034 q = 1) : d240884 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24022, d240884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24022, d240884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58912 (p : Pattern) (ha : d24028 p = 1) (hb : d208034 p = 1) : d240890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24023 q = 1) (hb : d208034 q = 1) : d240885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24023, d240885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58911 q ha hb
    | true =>
      simp only [d24023, d240885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58887 q ha hb
  have h2 (q : Pattern) (ha : d24024 q = 1) (hb : d208034 q = 1) : d240886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24024, d240886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24024, d240886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24025 q = 1) (hb : d208034 q = 1) : d240887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24025, d240887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24025, d240887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23953 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58887 q ha hb
    | true =>
      simp only [d23953, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
  have h5 (q : Pattern) (ha : d23954 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23955 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24026 q = 1) (hb : d208034 q = 1) : d240888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24026, d240888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24026, d240888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23957 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
    | true =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58889 q ha hb
  have h9 (q : Pattern) (ha : d23958 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23959 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23960 q = 1) (hb : d208034 q = 1) : d240824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23960, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24027 q = 1) (hb : d208034 q = 1) : d240889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24027, d240889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24027, d240889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24028 q = 1) (hb : d208034 q = 1) : d240890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24028, d240890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24028, d240890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58913 (p : Pattern) (ha : d24034 p = 1) (hb : d208034 p = 1) : d240896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24029 q = 1) (hb : d208034 q = 1) : d240891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24029, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58912 q ha hb
    | true =>
      simp only [d24029, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24030 q = 1) (hb : d208034 q = 1) : d240892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24030, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24030, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24031 q = 1) (hb : d208034 q = 1) : d240893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24031, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24031, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24032 q = 1) (hb : d208034 q = 1) : d240894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24032, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24032, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24033 q = 1) (hb : d208034 q = 1) : d240895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24033, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24033, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24034 q = 1) (hb : d208034 q = 1) : d240896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24034, d240896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24034, d240896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58914 (p : Pattern) (ha : d5539 p = 1) (hb : d208034 p = 1) : d240808 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5534 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5534, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5534, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5535 q = 1) (hb : d208034 q = 1) : d26090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5535, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5535, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5536 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5536, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5536, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1116 q = 1) : d1116 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1117 q = 1) (hb : d152852 q = 1) : d1132 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d5537 q = 1) (hb : d208034 q = 1) : d1133 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5537, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5537, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d5538 q = 1) (hb : d208034 q = 1) : d1134 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5538, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5538, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d5539 q = 1) (hb : d208034 q = 1) : d240808 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5539, d240808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5539, d240808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58915 (p : Pattern) (ha : d5546 p = 1) (hb : d208034 p = 1) : d240899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5540 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58914 q ha hb
    | true =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5541 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5542 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5542, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5543 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5543, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5544 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5544, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5546 q = 1) (hb : d208034 q = 1) : d240899 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5546, d240899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5546, d240899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58916 (p : Pattern) (ha : d24091 p = 1) (hb : d208034 p = 1) : d240816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23941 q = 1) (hb : d208034 q = 1) : d26103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23942 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23942, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23947 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23948 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23948, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23949 q = 1) (hb : d208034 q = 1) : d240813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23949, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5540 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58914 q ha hb
    | true =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5541 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5542 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5542, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5543 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5543, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5544 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5544, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24091 q = 1) (hb : d208034 q = 1) : d240816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24091, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24091, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58917 (p : Pattern) (ha : d24097 p = 1) (hb : d208034 p = 1) : d240905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23953 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58887 q ha hb
    | true =>
      simp only [d23953, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
  have h2 (q : Pattern) (ha : d23954 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23955 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23957 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58888 q ha hb
    | true =>
      simp only [d23957, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58889 q ha hb
  have h5 (q : Pattern) (ha : d23958 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23959 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23960 q = 1) (hb : d208034 q = 1) : d240824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23960, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24092 q = 1) (hb : d208034 q = 1) : d240900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24092, d240900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58916 q ha hb
    | true =>
      simp only [d24092, d240900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58915 q ha hb
  have h9 (q : Pattern) (ha : d24093 q = 1) (hb : d208034 q = 1) : d240901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24093, d240901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24093, d240901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24094 q = 1) (hb : d208034 q = 1) : d240902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24094, d240902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24094, d240902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24095 q = 1) (hb : d208034 q = 1) : d240903 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24095, d240903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24095, d240903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24096 q = 1) (hb : d208034 q = 1) : d240904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24096, d240904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24096, d240904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24097 q = 1) (hb : d208034 q = 1) : d240905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24097, d240905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24097, d240905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58918 (p : Pattern) (ha : d24103 p = 1) (hb : d208034 p = 1) : d240911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24098 q = 1) (hb : d208034 q = 1) : d240906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24098, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58917 q ha hb
    | true =>
      simp only [d24098, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24099 q = 1) (hb : d208034 q = 1) : d240907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24099, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24099, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24100 q = 1) (hb : d208034 q = 1) : d240908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24100, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24100, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24101 q = 1) (hb : d208034 q = 1) : d240909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24101, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24101, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24102 q = 1) (hb : d208034 q = 1) : d240910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24102, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24102, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24103 q = 1) (hb : d208034 q = 1) : d240911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24103, d240911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24103, d240911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58919 (p : Pattern) (ha : d208034 p = 1) (hb : d211244 p = 1) : d240917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24001 q = 1) (hb : d208034 q = 1) : d240865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24001, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58906 q ha hb
    | true =>
      simp only [d24001, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58907 q ha hb
  have h2 (q : Pattern) (ha : d24002 q = 1) (hb : d208034 q = 1) : d240866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24002, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24002, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24003 q = 1) (hb : d208034 q = 1) : d240867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24003, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24003, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24004 q = 1) (hb : d208034 q = 1) : d240868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24004, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24004, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24011 q = 1) (hb : d208034 q = 1) : d240875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24011, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58908 q ha hb
    | true =>
      simp only [d24011, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58909 q ha hb
  have h6 (q : Pattern) (ha : d24012 q = 1) (hb : d208034 q = 1) : d240876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24012, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24012, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24013 q = 1) (hb : d208034 q = 1) : d240877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24013, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24013, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24035 q = 1) (hb : d208034 q = 1) : d240897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24035, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58913 q ha hb
    | true =>
      simp only [d24035, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58892 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211240 q = 1) : d240898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211240, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d24104 q = 1) (hb : d208034 q = 1) : d240912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24104, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58918 q ha hb
    | true =>
      simp only [d24104, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24105 q = 1) (hb : d208034 q = 1) : d240913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24105, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24105, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211241 q = 1) : d240914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211241, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211242 q = 1) : d240915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211242, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211243 q = 1) : d240916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211243, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211244 q = 1) : d240917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211244, d240917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211244, d240917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58920 (p : Pattern) (ha : d24110 p = 1) (hb : d208034 p = 1) : d240918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23997 q = 1) (hb : d208034 q = 1) : d240861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23997, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23997, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24110 q = 1) (hb : d208034 q = 1) : d240918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24110, d240918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24110, d240918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58921 (p : Pattern) (ha : d24111 p = 1) (hb : d208034 p = 1) : d240919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23999 q = 1) (hb : d208034 q = 1) : d240863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23999, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23999, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24111 q = 1) (hb : d208034 q = 1) : d240919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24111, d240919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24111, d240919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58922 (p : Pattern) (ha : d24116 p = 1) (hb : d208034 p = 1) : d240924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24005 q = 1) (hb : d208034 q = 1) : d240869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24005, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24005, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24006 q = 1) (hb : d208034 q = 1) : d240870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24006, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24006, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24116 q = 1) (hb : d208034 q = 1) : d240924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24116, d240924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24116, d240924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58923 (p : Pattern) (ha : d24117 p = 1) (hb : d208034 p = 1) : d240925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58891 q ha hb
    | true =>
      simp only [d23968, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24008 q = 1) (hb : d208034 q = 1) : d240872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24008, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24008, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24009 q = 1) (hb : d208034 q = 1) : d240873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24009, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24009, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24117 q = 1) (hb : d208034 q = 1) : d240925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24117, d240925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24117, d240925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58924 (p : Pattern) (ha : d24121 p = 1) (hb : d208034 p = 1) : d240929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24029 q = 1) (hb : d208034 q = 1) : d240891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24029, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58912 q ha hb
    | true =>
      simp only [d24029, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24030 q = 1) (hb : d208034 q = 1) : d240892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24030, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24030, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23964 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58890 q ha hb
    | true =>
      simp only [d23964, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23965 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24031 q = 1) (hb : d208034 q = 1) : d240893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24031, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24031, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24032 q = 1) (hb : d208034 q = 1) : d240894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24032, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24032, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24033 q = 1) (hb : d208034 q = 1) : d240895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24033, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24033, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24121 q = 1) (hb : d208034 q = 1) : d240929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24121, d240929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24121, d240929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58925 (p : Pattern) (ha : d24127 p = 1) (hb : d208034 p = 1) : d240932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24098 q = 1) (hb : d208034 q = 1) : d240906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24098, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58917 q ha hb
    | true =>
      simp only [d24098, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24099 q = 1) (hb : d208034 q = 1) : d240907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24099, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24099, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24100 q = 1) (hb : d208034 q = 1) : d240908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24100, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24100, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24101 q = 1) (hb : d208034 q = 1) : d240909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24101, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24101, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24102 q = 1) (hb : d208034 q = 1) : d240910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24102, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24102, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24127 q = 1) (hb : d208034 q = 1) : d240932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24127, d240932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24127, d240932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58926 (p : Pattern) (ha : d208034 p = 1) (hb : d211249 p = 1) : d240938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24001 q = 1) (hb : d208034 q = 1) : d240865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24001, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58906 q ha hb
    | true =>
      simp only [d24001, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58907 q ha hb
  have h2 (q : Pattern) (ha : d24002 q = 1) (hb : d208034 q = 1) : d240866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24002, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24002, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24003 q = 1) (hb : d208034 q = 1) : d240867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24003, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24003, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24004 q = 1) (hb : d208034 q = 1) : d240868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24004, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24004, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24011 q = 1) (hb : d208034 q = 1) : d240875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24011, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58908 q ha hb
    | true =>
      simp only [d24011, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58909 q ha hb
  have h6 (q : Pattern) (ha : d24012 q = 1) (hb : d208034 q = 1) : d240876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24012, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24012, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24013 q = 1) (hb : d208034 q = 1) : d240877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24013, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24013, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24035 q = 1) (hb : d208034 q = 1) : d240897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24035, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58913 q ha hb
    | true =>
      simp only [d24035, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58892 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211240 q = 1) : d240898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211240, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d24104 q = 1) (hb : d208034 q = 1) : d240912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24104, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58918 q ha hb
    | true =>
      simp only [d24104, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24105 q = 1) (hb : d208034 q = 1) : d240913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24105, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24105, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211241 q = 1) : d240914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211241, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211242 q = 1) : d240915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211242, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211243 q = 1) : d240916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211243, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24112 q = 1) (hb : d208034 q = 1) : d240920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24112, d240920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58920 q ha hb
    | true =>
      simp only [d24112, d240920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58921 q ha hb
  have h16 (q : Pattern) (ha : d24113 q = 1) (hb : d208034 q = 1) : d240921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24113, d240921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24113, d240921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24114 q = 1) (hb : d208034 q = 1) : d240922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24114, d240922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24114, d240922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24115 q = 1) (hb : d208034 q = 1) : d240923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24115, d240923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24115, d240923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24118 q = 1) (hb : d208034 q = 1) : d240926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24118, d240926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58922 q ha hb
    | true =>
      simp only [d24118, d240926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58923 q ha hb
  have h20 (q : Pattern) (ha : d24119 q = 1) (hb : d208034 q = 1) : d240927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24119, d240927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24119, d240927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24120 q = 1) (hb : d208034 q = 1) : d240928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24120, d240928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d24120, d240928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d24122 q = 1) (hb : d208034 q = 1) : d240930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24122, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58924 q ha hb
    | true =>
      simp only [d24122, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58895 q ha hb
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211245 q = 1) : d240931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d211245, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d24128 q = 1) (hb : d208034 q = 1) : d240933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24128, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58925 q ha hb
    | true =>
      simp only [d24128, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d24129 q = 1) (hb : d208034 q = 1) : d240934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24129, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d24129, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d208034 q = 1) (hb : d211246 q = 1) : d240935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211246, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d208034 q = 1) (hb : d211247 q = 1) : d240936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211247, d240936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211247, d240936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d208034 q = 1) (hb : d211248 q = 1) : d240937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211248, d240937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d211248, d240937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d208034 q = 1) (hb : d211249 q = 1) : d240938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211249, d240938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211249, d240938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro58927 (p : Pattern) (ha : d208034 p = 1) (hb : d211256 p = 1) : d240958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24122 q = 1) (hb : d208034 q = 1) : d240930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24122, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58924 q ha hb
    | true =>
      simp only [d24122, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58895 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211245 q = 1) : d240931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211245, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d24128 q = 1) (hb : d208034 q = 1) : d240933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24128, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58925 q ha hb
    | true =>
      simp only [d24128, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24129 q = 1) (hb : d208034 q = 1) : d240934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24129, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24129, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211246 q = 1) : d240935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211246, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211254 q = 1) : d240956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211254, d240956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211254, d240956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211255 q = 1) : d240957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211255, d240957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211255, d240957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211256 q = 1) : d240958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211256, d240958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211256, d240958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58928 (p : Pattern) (ha : d24175 p = 1) (hb : d208034 p = 1) : d240971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24161 q = 1) (hb : d208034 q = 1) : d240966 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24161, d240966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24161, d240966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58910 q ha hb
  have h2 (q : Pattern) (ha : d24017 q = 1) (hb : d208034 q = 1) : d240879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24017, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58910 q ha hb
    | true =>
      simp only [d24017, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24162 q = 1) (hb : d208034 q = 1) : d240967 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24162, d240967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24162, d240967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24018 q = 1) (hb : d208034 q = 1) : d240880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24018, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24018, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24163 q = 1) (hb : d208034 q = 1) : d240968 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24163, d240968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24163, d240968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24164 q = 1) (hb : d208034 q = 1) : d240969 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24164, d240969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24164, d240969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24165 q = 1) (hb : d208034 q = 1) : d26382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24165, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24165, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58884 q ha hb
  have h8 (q : Pattern) (ha : d23932 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58884 q ha hb
    | true =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24166 q = 1) (hb : d208034 q = 1) : d26383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24166, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24166, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23933 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24167 q = 1) (hb : d208034 q = 1) : d26384 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24167, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24167, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24168 q = 1) (hb : d208034 q = 1) : d26385 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24168, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24168, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24169 q = 1) (hb : d208034 q = 1) : d240970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24169, d240970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24169, d240970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24170 q = 1) (hb : d208034 q = 1) : d26386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
  have h15 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24171 q = 1) (hb : d208034 q = 1) : d26387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24172 q = 1) (hb : d208034 q = 1) : d26388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24173 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24174 q = 1) (hb : d208034 q = 1) : d26390 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24174, d26390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24174, d26390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24175 q = 1) (hb : d208034 q = 1) : d240971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24175, d240971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24175, d240971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58929 (p : Pattern) (ha : d24181 p = 1) (hb : d208034 p = 1) : d240977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24165 q = 1) (hb : d208034 q = 1) : d26382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24165, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24165, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58884 q ha hb
  have h2 (q : Pattern) (ha : d23932 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58884 q ha hb
    | true =>
      simp only [d23932, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24166 q = 1) (hb : d208034 q = 1) : d26383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24166, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24166, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23933 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23933, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24167 q = 1) (hb : d208034 q = 1) : d26384 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24167, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24167, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24168 q = 1) (hb : d208034 q = 1) : d26385 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24168, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24168, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24170 q = 1) (hb : d208034 q = 1) : d26386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
  have h8 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24171 q = 1) (hb : d208034 q = 1) : d26387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24172 q = 1) (hb : d208034 q = 1) : d26388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24173 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24174 q = 1) (hb : d208034 q = 1) : d26390 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24174, d26390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24174, d26390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24176 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
  have h15 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24177 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24178 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24179 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24180 q = 1) (hb : d208034 q = 1) : d240976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24180, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24180, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24181 q = 1) (hb : d208034 q = 1) : d240977 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24181, d240977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24181, d240977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58930 (p : Pattern) (ha : d24197 p = 1) (hb : d208034 p = 1) : d240993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24182 q = 1) (hb : d208034 q = 1) : d240978 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24182, d240978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58928 q ha hb
    | true =>
      simp only [d24182, d240978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58929 q ha hb
  have h2 (q : Pattern) (ha : d24183 q = 1) (hb : d208034 q = 1) : d240979 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24183, d240979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24183, d240979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24184 q = 1) (hb : d208034 q = 1) : d240980 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24184, d240980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24184, d240980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24187 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24187, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58929 q ha hb
    | true =>
      simp only [d24187, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
  have h5 (q : Pattern) (ha : d24188 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24188, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24188, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24189 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24189, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24189, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24190 q = 1) (hb : d208034 q = 1) : d240986 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24190, d240986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24190, d240986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24192 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
    | true =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58902 q ha hb
  have h9 (q : Pattern) (ha : d24193 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24194 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24195 q = 1) (hb : d208034 q = 1) : d240991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24195, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24195, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24196 q = 1) (hb : d208034 q = 1) : d240992 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24196, d240992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24196, d240992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24197 q = 1) (hb : d208034 q = 1) : d240993 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24197, d240993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24197, d240993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58931 (p : Pattern) (ha : d24202 p = 1) (hb : d208034 p = 1) : d240998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24187 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24187, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58929 q ha hb
    | true =>
      simp only [d24187, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
  have h2 (q : Pattern) (ha : d24188 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24188, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24188, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24189 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24189, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24189, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24192 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
    | true =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58902 q ha hb
  have h5 (q : Pattern) (ha : d24193 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24194 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24195 q = 1) (hb : d208034 q = 1) : d240991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24195, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24195, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24200 q = 1) (hb : d208034 q = 1) : d240996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24200, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24200, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24201 q = 1) (hb : d208034 q = 1) : d240997 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24201, d240997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24201, d240997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24202 q = 1) (hb : d208034 q = 1) : d240998 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24202, d240998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24202, d240998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58932 (p : Pattern) (ha : d24208 p = 1) (hb : d208034 p = 1) : d241004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24198 q = 1) (hb : d208034 q = 1) : d240994 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24198, d240994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58930 q ha hb
    | true =>
      simp only [d24198, d240994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24199 q = 1) (hb : d208034 q = 1) : d240995 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24199, d240995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24199, d240995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24203 q = 1) (hb : d208034 q = 1) : d240999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24203, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58931 q ha hb
    | true =>
      simp only [d24203, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24204 q = 1) (hb : d208034 q = 1) : d241000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24204, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24204, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24205 q = 1) (hb : d208034 q = 1) : d241001 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24205, d241001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24205, d241001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24206 q = 1) (hb : d208034 q = 1) : d241002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24206, d241002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24206, d241002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24207 q = 1) (hb : d208034 q = 1) : d241003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24207, d241003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24207, d241003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24208 q = 1) (hb : d208034 q = 1) : d241004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24208, d241004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24208, d241004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58933 (p : Pattern) (ha : d24216 p = 1) (hb : d208034 p = 1) : d241012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24203 q = 1) (hb : d208034 q = 1) : d240999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24203, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58931 q ha hb
    | true =>
      simp only [d24203, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24204 q = 1) (hb : d208034 q = 1) : d241000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24204, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24204, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24211 q = 1) (hb : d208034 q = 1) : d241007 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24211, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58903 q ha hb
    | true =>
      simp only [d24211, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24212 q = 1) (hb : d208034 q = 1) : d241008 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24212, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24212, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24213 q = 1) (hb : d208034 q = 1) : d241009 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24213, d241009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24213, d241009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24214 q = 1) (hb : d208034 q = 1) : d241010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24214, d241010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24214, d241010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24215 q = 1) (hb : d208034 q = 1) : d241011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24215, d241011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24215, d241011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24216 q = 1) (hb : d208034 q = 1) : d241012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24216, d241012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24216, d241012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58934 (p : Pattern) (ha : d5590 p = 1) (hb : d208034 p = 1) : d241015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5584 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5584, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58914 q ha hb
  have h2 (q : Pattern) (ha : d5540 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58914 q ha hb
    | true =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5585 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5585, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5541 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5586 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5586, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5587 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5587, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5588 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5588, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5590 q = 1) (hb : d208034 q = 1) : d241015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5590, d241015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5590, d241015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58935 (p : Pattern) (ha : d24262 p = 1) (hb : d208034 p = 1) : d240982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24170 q = 1) (hb : d208034 q = 1) : d26386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
  have h2 (q : Pattern) (ha : d23939 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58885 q ha hb
    | true =>
      simp only [d23939, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24171 q = 1) (hb : d208034 q = 1) : d26387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24171, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23940 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23940, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24172 q = 1) (hb : d208034 q = 1) : d26388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24172, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24173 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24173, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24176 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
  have h8 (q : Pattern) (ha : d23945 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58886 q ha hb
    | true =>
      simp only [d23945, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24177 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24177, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23946 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23946, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24178 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24178, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24179 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24179, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24180 q = 1) (hb : d208034 q = 1) : d240976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24180, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24180, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5584 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5584, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58914 q ha hb
  have h15 (q : Pattern) (ha : d5540 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58914 q ha hb
    | true =>
      simp only [d5540, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5585 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5585, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5541 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5541, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5586 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5586, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5587 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5587, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5588 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5588, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d24262 q = 1) (hb : d208034 q = 1) : d240982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24262, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24262, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58936 (p : Pattern) (ha : d24268 p = 1) (hb : d208034 p = 1) : d241021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24187 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24187, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58929 q ha hb
    | true =>
      simp only [d24187, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
  have h2 (q : Pattern) (ha : d24188 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24188, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24188, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24189 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24189, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24189, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24192 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58901 q ha hb
    | true =>
      simp only [d24192, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58902 q ha hb
  have h5 (q : Pattern) (ha : d24193 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24193, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24194 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24194, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24195 q = 1) (hb : d208034 q = 1) : d240991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24195, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24195, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24263 q = 1) (hb : d208034 q = 1) : d241016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24263, d241016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58935 q ha hb
    | true =>
      simp only [d24263, d241016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58934 q ha hb
  have h9 (q : Pattern) (ha : d24264 q = 1) (hb : d208034 q = 1) : d241017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24264, d241017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24264, d241017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24265 q = 1) (hb : d208034 q = 1) : d241018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24265, d241018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24265, d241018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24266 q = 1) (hb : d208034 q = 1) : d241019 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24266, d241019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24266, d241019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24267 q = 1) (hb : d208034 q = 1) : d241020 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24267, d241020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24267, d241020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24268 q = 1) (hb : d208034 q = 1) : d241021 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24268, d241021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24268, d241021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58937 (p : Pattern) (ha : d24274 p = 1) (hb : d208034 p = 1) : d241027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24269 q = 1) (hb : d208034 q = 1) : d241022 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24269, d241022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58936 q ha hb
    | true =>
      simp only [d24269, d241022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24270 q = 1) (hb : d208034 q = 1) : d241023 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24270, d241023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24270, d241023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24271 q = 1) (hb : d208034 q = 1) : d241024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24271, d241024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24271, d241024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24272 q = 1) (hb : d208034 q = 1) : d241025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24272, d241025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24272, d241025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24273 q = 1) (hb : d208034 q = 1) : d241026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24273, d241026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24273, d241026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24274 q = 1) (hb : d208034 q = 1) : d241027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24274, d241027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24274, d241027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58938 (p : Pattern) (ha : d208034 p = 1) (hb : d211266 p = 1) : d241033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24217 q = 1) (hb : d208034 q = 1) : d241013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24217, d241013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58932 q ha hb
    | true =>
      simp only [d24217, d241013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58933 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211262 q = 1) : d241014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211262, d241014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211262, d241014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d24275 q = 1) (hb : d208034 q = 1) : d241028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24275, d241028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58937 q ha hb
    | true =>
      simp only [d24275, d241028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24276 q = 1) (hb : d208034 q = 1) : d241029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24276, d241029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24276, d241029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211263 q = 1) : d241030 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211263, d241030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211263, d241030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211264 q = 1) : d241031 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211264, d241031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211264, d241031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211265 q = 1) : d241032 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211265, d241032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211265, d241032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211266 q = 1) : d241033 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211266, d241033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211266, d241033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58939 (p : Pattern) (ha : d208034 p = 1) (hb : d211272 p = 1) : d241050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23984 q = 1) (hb : d208034 q = 1) : d240848 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23984, d240848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23984, d240848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58894 q ha hb
  have h2 (q : Pattern) (ha : d23985 q = 1) (hb : d208034 q = 1) : d240849 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23985, d240849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23985, d240849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23994 q = 1) (hb : d208034 q = 1) : d240858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58894 q ha hb
    | true =>
      simp only [d23994, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58897 q ha hb
  have h4 (q : Pattern) (ha : d23995 q = 1) (hb : d208034 q = 1) : d240859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23995, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23996 q = 1) (hb : d208034 q = 1) : d240860 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23996, d240860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23996, d240860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211250 q = 1) : d240939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211250, d240939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58919 q ha hb
    | true =>
      simp only [d211250, d240939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58926 q ha hb
  have h7 (q : Pattern) (ha : d24147 q = 1) (hb : d208034 q = 1) : d240952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24147, d240952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58898 q ha hb
    | true =>
      simp only [d24147, d240952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58899 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211251 q = 1) : d240953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211251, d240953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211251, d240953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211252 q = 1) : d240954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211252, d240954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211252, d240954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211253 q = 1) : d240955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211253, d240955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211253, d240955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211257 q = 1) : d240959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211257, d240959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211257, d240959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58927 q ha hb
  have h12 (q : Pattern) (ha : d24156 q = 1) (hb : d208034 q = 1) : d240961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24156, d240961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24156, d240961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58900 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211258 q = 1) : d240962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211258, d240962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211258, d240962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211259 q = 1) : d240963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211259, d240963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211259, d240963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211260 q = 1) : d240964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211260, d240964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211260, d240964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211261 q = 1) : d240965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211261, d240965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211261, d240965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211267 q = 1) : d241034 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211267, d241034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211267, d241034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58938 q ha hb
  have h18 (q : Pattern) (ha : d24292 q = 1) (hb : d208034 q = 1) : d241045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24292, d241045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24292, d241045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58905 q ha hb
  have h19 (q : Pattern) (ha : d208034 q = 1) (hb : d211268 q = 1) : d241046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211268, d241046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211268, d241046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d208034 q = 1) (hb : d211269 q = 1) : d241047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211269, d241047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211269, d241047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208034 q = 1) (hb : d211270 q = 1) : d241048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211270, d241048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211270, d241048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208034 q = 1) (hb : d211271 q = 1) : d241049 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211271, d241049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211271, d241049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211272 q = 1) : d241050 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211272, d241050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211272, d241050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro58940 (p : Pattern) (ha : d208034 p = 1) (hb : d211278 p = 1) : d241056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d211273 q = 1) : d241051 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211273, d241051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211273, d241051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58939 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211274 q = 1) : d241052 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211274, d241052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211274, d241052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211275 q = 1) : d241053 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211275, d241053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211275, d241053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d211276 q = 1) : d241054 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211276, d241054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211276, d241054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211277 q = 1) : d241055 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211277, d241055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211277, d241055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211278 q = 1) : d241056 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211278, d241056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211278, d241056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58941 (p : Pattern) (ha : d24311 p = 1) (hb : d208034 p = 1) : d26658 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1201 q = 1) : d1201 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1530 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24307 q = 1) (hb : d208034 q = 1) : d10043 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24307, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24307, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24308 q = 1) (hb : d208034 q = 1) : d10044 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24308, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24308, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1546 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d24309 q = 1) (hb : d208034 q = 1) : d10052 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24309, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24309, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d24310 q = 1) (hb : d208034 q = 1) : d10053 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24310, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24310, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24311 q = 1) (hb : d208034 q = 1) : d26658 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24311, d26658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24311, d26658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58942 (p : Pattern) (ha : d24318 p = 1) (hb : d208034 p = 1) : d26567 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1546 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24309 q = 1) (hb : d208034 q = 1) : d10052 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24309, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24309, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24310 q = 1) (hb : d208034 q = 1) : d10053 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24310, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24310, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1561 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1562 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d24316 q = 1) (hb : d208034 q = 1) : d26559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24316, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24316, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d24317 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24317, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24317, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24318 q = 1) (hb : d208034 q = 1) : d26567 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24318, d26567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24318, d26567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58943 (p : Pattern) (ha : d24326 p = 1) (hb : d208034 p = 1) : d241060 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1562 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24316 q = 1) (hb : d208034 q = 1) : d26559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24316, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24316, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24317 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24317, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24317, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1576 q = 1) : d1576 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1577 q = 1) (hb : d152852 q = 1) : d1593 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d152852, d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1577, d152852, d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d24324 q = 1) (hb : d208034 q = 1) : d1594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24324, d208034, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24324, d208034, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d24325 q = 1) (hb : d208034 q = 1) : d1595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24325, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24325, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24326 q = 1) (hb : d208034 q = 1) : d241060 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24326, d241060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24326, d241060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58944 (p : Pattern) (ha : d24332 p = 1) (hb : d208034 p = 1) : d241066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24312 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58941 q ha hb
    | true =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24313 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24314 q = 1) (hb : d208034 q = 1) : d26661 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24314, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24314, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24315 q = 1) (hb : d208034 q = 1) : d26662 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24315, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24315, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24321 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24322 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24323 q = 1) (hb : d208034 q = 1) : d26663 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24323, d26663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24323, d26663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24329 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24330 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d24331 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24331, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24331, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24332 q = 1) (hb : d208034 q = 1) : d241066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24332, d241066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24332, d241066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58945 (p : Pattern) (ha : d24334 p = 1) (hb : d208034 p = 1) : d241068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24321 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24322 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24329 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24330 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24331 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24331, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24331, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24333 q = 1) (hb : d208034 q = 1) : d241067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24333, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24333, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24334 q = 1) (hb : d208034 q = 1) : d241068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24334, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24334, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58946 (p : Pattern) (ha : d24338 p = 1) (hb : d208034 p = 1) : d241072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24329 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24330 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24333 q = 1) (hb : d208034 q = 1) : d241067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24333, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24333, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1601 q = 1) (hb : d208034 q = 1) : d1601 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24338 q = 1) (hb : d208034 q = 1) : d241072 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24338, d241072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24338, d241072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro58947 (p : Pattern) (ha : d24345 p = 1) (hb : d208034 p = 1) : d241079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24335 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24335, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58944 q ha hb
    | true =>
      simp only [d24335, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
  have h2 (q : Pattern) (ha : d24336 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24336, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24336, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24337 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24337, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24337, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24339 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
    | true =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58946 q ha hb
  have h5 (q : Pattern) (ha : d24340 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24341 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24342 q = 1) (hb : d208034 q = 1) : d241076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24342, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24342, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24343 q = 1) (hb : d208034 q = 1) : d241077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24343, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24343, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24344 q = 1) (hb : d208034 q = 1) : d241078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24344, d241078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24344, d241078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24345 q = 1) (hb : d208034 q = 1) : d241079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24345, d241079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24345, d241079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58948 (p : Pattern) (ha : d24349 p = 1) (hb : d208034 p = 1) : d241083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24339 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
    | true =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58946 q ha hb
  have h2 (q : Pattern) (ha : d24340 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24341 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24343 q = 1) (hb : d208034 q = 1) : d241077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24343, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24343, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24348 q = 1) (hb : d208034 q = 1) : d241082 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24348, d241082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24348, d241082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24349 q = 1) (hb : d208034 q = 1) : d241083 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24349, d241083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24349, d241083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58949 (p : Pattern) (ha : d24355 p = 1) (hb : d208034 p = 1) : d241089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24353 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24354 q = 1) (hb : d208034 q = 1) : d241088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24354, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24354, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24355 q = 1) (hb : d208034 q = 1) : d241089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24355, d241089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24355, d241089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58950 (p : Pattern) (ha : d24359 p = 1) (hb : d208034 p = 1) : d241093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24357 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24358 q = 1) (hb : d208034 q = 1) : d241092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24358, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24358, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24359 q = 1) (hb : d208034 q = 1) : d241093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24359, d241093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24359, d241093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58951 (p : Pattern) (ha : d24365 p = 1) (hb : d208034 p = 1) : d241099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24360 q = 1) (hb : d208034 q = 1) : d241094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58949 q ha hb
    | true =>
      simp only [d24360, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58950 q ha hb
  have h2 (q : Pattern) (ha : d24361 q = 1) (hb : d208034 q = 1) : d241095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24361, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24362 q = 1) (hb : d208034 q = 1) : d241096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24362, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24363 q = 1) (hb : d208034 q = 1) : d241097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24363, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24364 q = 1) (hb : d208034 q = 1) : d241098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24365 q = 1) (hb : d208034 q = 1) : d241099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24365, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24365, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58952 (p : Pattern) (ha : d24368 p = 1) (hb : d208034 p = 1) : d241102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24353 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24354 q = 1) (hb : d208034 q = 1) : d241088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24354, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24354, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24368 q = 1) (hb : d208034 q = 1) : d241102 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24368, d241102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24368, d241102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58953 (p : Pattern) (ha : d24369 p = 1) (hb : d208034 p = 1) : d241103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24357 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24358 q = 1) (hb : d208034 q = 1) : d241092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24358, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24358, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24369 q = 1) (hb : d208034 q = 1) : d241103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24369, d241103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24369, d241103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58954 (p : Pattern) (ha : d24375 p = 1) (hb : d208034 p = 1) : d241109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24360 q = 1) (hb : d208034 q = 1) : d241094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58949 q ha hb
    | true =>
      simp only [d24360, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58950 q ha hb
  have h2 (q : Pattern) (ha : d24361 q = 1) (hb : d208034 q = 1) : d241095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24361, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24362 q = 1) (hb : d208034 q = 1) : d241096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24362, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24363 q = 1) (hb : d208034 q = 1) : d241097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24363, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24364 q = 1) (hb : d208034 q = 1) : d241098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24370 q = 1) (hb : d208034 q = 1) : d241104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58952 q ha hb
    | true =>
      simp only [d24370, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58953 q ha hb
  have h7 (q : Pattern) (ha : d24371 q = 1) (hb : d208034 q = 1) : d241105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24371, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24372 q = 1) (hb : d208034 q = 1) : d241106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24372, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24373 q = 1) (hb : d208034 q = 1) : d241107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24374 q = 1) (hb : d208034 q = 1) : d241108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24375 q = 1) (hb : d208034 q = 1) : d241109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24375, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24375, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58955 (p : Pattern) (ha : d24522 p = 1) (hb : d208034 p = 1) : d241199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24360 q = 1) (hb : d208034 q = 1) : d241094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58949 q ha hb
    | true =>
      simp only [d24360, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58950 q ha hb
  have h2 (q : Pattern) (ha : d24361 q = 1) (hb : d208034 q = 1) : d241095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24361, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24362 q = 1) (hb : d208034 q = 1) : d241096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24362, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24363 q = 1) (hb : d208034 q = 1) : d241097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24363, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24364 q = 1) (hb : d208034 q = 1) : d241098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24517 q = 1) (hb : d208034 q = 1) : d241194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24517, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58950 q ha hb
    | true =>
      simp only [d24517, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24518 q = 1) (hb : d208034 q = 1) : d241195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24518, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24518, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24519 q = 1) (hb : d208034 q = 1) : d241196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24519, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24519, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24520 q = 1) (hb : d208034 q = 1) : d241197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24520, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24520, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24521 q = 1) (hb : d208034 q = 1) : d241198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24521, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24521, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24522 q = 1) (hb : d208034 q = 1) : d241199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24522, d241199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24522, d241199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58956 (p : Pattern) (ha : d24528 p = 1) (hb : d208034 p = 1) : d241205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24517 q = 1) (hb : d208034 q = 1) : d241194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24517, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58950 q ha hb
    | true =>
      simp only [d24517, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24518 q = 1) (hb : d208034 q = 1) : d241195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24518, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24518, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24519 q = 1) (hb : d208034 q = 1) : d241196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24519, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24519, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24520 q = 1) (hb : d208034 q = 1) : d241197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24520, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24520, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24521 q = 1) (hb : d208034 q = 1) : d241198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24521, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24521, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24523 q = 1) (hb : d208034 q = 1) : d241200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24523, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58953 q ha hb
    | true =>
      simp only [d24523, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24524 q = 1) (hb : d208034 q = 1) : d241201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24524, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24524, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24525 q = 1) (hb : d208034 q = 1) : d241202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24525, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24525, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24526 q = 1) (hb : d208034 q = 1) : d241203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24526, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24526, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24527 q = 1) (hb : d208034 q = 1) : d241204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24527, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24527, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24528 q = 1) (hb : d208034 q = 1) : d241205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24528, d241205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24528, d241205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58957 (p : Pattern) (ha : d24537 p = 1) (hb : d208034 p = 1) : d241214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24523 q = 1) (hb : d208034 q = 1) : d241200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24523, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58953 q ha hb
    | true =>
      simp only [d24523, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24524 q = 1) (hb : d208034 q = 1) : d241201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24524, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24524, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24525 q = 1) (hb : d208034 q = 1) : d241202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24525, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24525, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24526 q = 1) (hb : d208034 q = 1) : d241203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24526, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24526, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24527 q = 1) (hb : d208034 q = 1) : d241204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24527, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24527, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24537 q = 1) (hb : d208034 q = 1) : d241214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24537, d241214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24537, d241214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58958 (p : Pattern) (ha : d24568 p = 1) (hb : d208034 p = 1) : d241232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24552 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
  have h2 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24553 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24554 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24555 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24558 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
  have h8 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24559 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24560 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24561 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24562 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24562, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24562, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24567 q = 1) (hb : d208034 q = 1) : d241231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24567, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24567, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24568 q = 1) (hb : d208034 q = 1) : d241232 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24568, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24568, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58959 (p : Pattern) (ha : d24573 p = 1) (hb : d208034 p = 1) : d241237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24558 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
  have h2 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24559 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24560 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24561 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24567 q = 1) (hb : d208034 q = 1) : d241231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24567, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24567, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1887 q = 1) (hb : d208034 q = 1) : d1887 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d24573 q = 1) (hb : d208034 q = 1) : d241237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24573, d241237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24573, d241237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro58960 (p : Pattern) (ha : d24592 p = 1) (hb : d208034 p = 1) : d241256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24574 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
    | true =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58959 q ha hb
  have h2 (q : Pattern) (ha : d24575 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24576 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24582 q = 1) (hb : d208034 q = 1) : d241246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24582, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24582, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24591 q = 1) (hb : d208034 q = 1) : d241255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24591, d241255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24591, d241255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24592 q = 1) (hb : d208034 q = 1) : d241256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24592, d241256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24592, d241256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58961 (p : Pattern) (ha : d24667 p = 1) (hb : d208034 p = 1) : d241294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24593 q = 1) (hb : d208034 q = 1) : d241257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24593, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58960 q ha hb
    | true =>
      simp only [d24593, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24594 q = 1) (hb : d208034 q = 1) : d241258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24594, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24594, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24664 q = 1) (hb : d208034 q = 1) : d241291 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24664, d241291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24664, d241291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24665 q = 1) (hb : d208034 q = 1) : d241292 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24665, d241292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24665, d241292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24666 q = 1) (hb : d208034 q = 1) : d241293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24666, d241293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24666, d241293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24667 q = 1) (hb : d208034 q = 1) : d241294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24667, d241294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24667, d241294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58962 (p : Pattern) (ha : d24673 p = 1) (hb : d208034 p = 1) : d241300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24668 q = 1) (hb : d208034 q = 1) : d241295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24668, d241295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58961 q ha hb
    | true =>
      simp only [d24668, d241295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24669 q = 1) (hb : d208034 q = 1) : d241296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24669, d241296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24669, d241296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24670 q = 1) (hb : d208034 q = 1) : d241297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24670, d241297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24670, d241297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24671 q = 1) (hb : d208034 q = 1) : d241298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24671, d241298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24671, d241298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24672 q = 1) (hb : d208034 q = 1) : d241299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24672, d241299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24672, d241299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24673 q = 1) (hb : d208034 q = 1) : d241300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24673, d241300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24673, d241300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58963 (p : Pattern) (ha : d24380 p = 1) (hb : d208034 p = 1) : d241114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24353 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24379 q = 1) (hb : d208034 q = 1) : d241113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24379, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24379, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24380 q = 1) (hb : d208034 q = 1) : d241114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24380, d241114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24380, d241114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58964 (p : Pattern) (ha : d24382 p = 1) (hb : d208034 p = 1) : d241116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24357 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24381 q = 1) (hb : d208034 q = 1) : d241115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24381, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24381, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24382 q = 1) (hb : d208034 q = 1) : d241116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24382, d241116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24382, d241116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58965 (p : Pattern) (ha : d24389 p = 1) (hb : d208034 p = 1) : d241123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24387 q = 1) (hb : d208034 q = 1) : d241121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24387, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24387, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24388 q = 1) (hb : d208034 q = 1) : d241122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24388, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24388, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24389 q = 1) (hb : d208034 q = 1) : d241123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24389, d241123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24389, d241123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58966 (p : Pattern) (ha : d24392 p = 1) (hb : d208034 p = 1) : d241126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24390 q = 1) (hb : d208034 q = 1) : d241124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24390, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24390, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24391 q = 1) (hb : d208034 q = 1) : d241125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24391, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24391, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24392 q = 1) (hb : d208034 q = 1) : d241126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24392, d241126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24392, d241126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58967 (p : Pattern) (ha : d24398 p = 1) (hb : d208034 p = 1) : d26652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1201 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1660 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1660, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1660, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24396 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24396, d208034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24396, d208034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24397 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1201 q = 1) : d1201 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1530 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d24307 q = 1) (hb : d208034 q = 1) : d10043 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24307, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24307, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d24308 q = 1) (hb : d208034 q = 1) : d10044 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24308, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24308, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24398 q = 1) (hb : d208034 q = 1) : d26652 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24398, d26652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24398, d26652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58968 (p : Pattern) (ha : d24404 p = 1) (hb : d208034 p = 1) : d241131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24399 q = 1) (hb : d208034 q = 1) : d26653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24399, d26653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58967 q ha hb
    | true =>
      simp only [d24399, d26653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24400 q = 1) (hb : d208034 q = 1) : d26654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24400, d26654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24400, d26654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24401 q = 1) (hb : d208034 q = 1) : d26655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24401, d26655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24401, d26655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24402 q = 1) (hb : d208034 q = 1) : d26656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24402, d26656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24402, d26656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24312 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58941 q ha hb
    | true =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24313 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24314 q = 1) (hb : d208034 q = 1) : d26661 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24314, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24314, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24315 q = 1) (hb : d208034 q = 1) : d26662 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24315, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24315, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24403 q = 1) (hb : d208034 q = 1) : d241130 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24403, d241130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24403, d241130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24321 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24322 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d24323 q = 1) (hb : d208034 q = 1) : d26663 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24323, d26663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24323, d26663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24404 q = 1) (hb : d208034 q = 1) : d241131 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24404, d241131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24404, d241131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58969 (p : Pattern) (ha : d24410 p = 1) (hb : d208034 p = 1) : d241137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24405 q = 1) (hb : d208034 q = 1) : d241132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24405, d241132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58968 q ha hb
    | true =>
      simp only [d24405, d241132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58944 q ha hb
  have h2 (q : Pattern) (ha : d24406 q = 1) (hb : d208034 q = 1) : d241133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24406, d241133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24406, d241133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24407 q = 1) (hb : d208034 q = 1) : d241134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24407, d241134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24407, d241134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24335 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24335, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58944 q ha hb
    | true =>
      simp only [d24335, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
  have h5 (q : Pattern) (ha : d24336 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24336, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24336, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24337 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24337, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24337, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24408 q = 1) (hb : d208034 q = 1) : d241135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24408, d241135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24408, d241135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24339 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
    | true =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58946 q ha hb
  have h9 (q : Pattern) (ha : d24340 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24341 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24342 q = 1) (hb : d208034 q = 1) : d241076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24342, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24342, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24409 q = 1) (hb : d208034 q = 1) : d241136 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24409, d241136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24409, d241136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24410 q = 1) (hb : d208034 q = 1) : d241137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24410, d241137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24410, d241137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58970 (p : Pattern) (ha : d24416 p = 1) (hb : d208034 p = 1) : d241143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24411 q = 1) (hb : d208034 q = 1) : d241138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24411, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58969 q ha hb
    | true =>
      simp only [d24411, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24412 q = 1) (hb : d208034 q = 1) : d241139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24412, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24412, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24413 q = 1) (hb : d208034 q = 1) : d241140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24413, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24413, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24414 q = 1) (hb : d208034 q = 1) : d241141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24414, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24414, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24415 q = 1) (hb : d208034 q = 1) : d241142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24415, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24415, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24416 q = 1) (hb : d208034 q = 1) : d241143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24416, d241143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24416, d241143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58971 (p : Pattern) (ha : d5629 p = 1) (hb : d208034 p = 1) : d241146 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5624 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5624, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5624, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5625 q = 1) (hb : d208034 q = 1) : d26559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5625, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5625, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5626 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5626, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5626, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d5129 q = 1) : d5129 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5130 q = 1) (hb : d152852 q = 1) : d26754 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d152852, d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d5130, d152852, d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d5627 q = 1) (hb : d208034 q = 1) : d239545 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5627, d208034, d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5627, d208034, d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d5628 q = 1) (hb : d208034 q = 1) : d239546 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5628, d239546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5628, d239546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d5629 q = 1) (hb : d208034 q = 1) : d241146 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5629, d241146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5629, d241146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58972 (p : Pattern) (ha : d5636 p = 1) (hb : d208034 p = 1) : d241153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5630 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58971 q ha hb
    | true =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5631 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5632 q = 1) (hb : d208034 q = 1) : d241149 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5632, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5633 q = 1) (hb : d208034 q = 1) : d241150 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5633, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5634 q = 1) (hb : d208034 q = 1) : d241151 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5634, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5636 q = 1) (hb : d208034 q = 1) : d241153 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5636, d241153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5636, d241153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58973 (p : Pattern) (ha : d24473 p = 1) (hb : d208034 p = 1) : d241152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24321 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24321, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24322 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24322, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24329 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24329, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24330 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24330, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24331 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24331, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24331, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5630 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58971 q ha hb
    | true =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5631 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5632 q = 1) (hb : d208034 q = 1) : d241149 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5632, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5633 q = 1) (hb : d208034 q = 1) : d241150 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5633, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5634 q = 1) (hb : d208034 q = 1) : d241151 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5634, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24473 q = 1) (hb : d208034 q = 1) : d241152 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24473, d241152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24473, d241152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58974 (p : Pattern) (ha : d24479 p = 1) (hb : d208034 p = 1) : d241159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24335 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24335, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58944 q ha hb
    | true =>
      simp only [d24335, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
  have h2 (q : Pattern) (ha : d24336 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24336, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24336, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24337 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24337, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24337, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24339 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58945 q ha hb
    | true =>
      simp only [d24339, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58946 q ha hb
  have h5 (q : Pattern) (ha : d24340 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24340, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24341 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24341, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24342 q = 1) (hb : d208034 q = 1) : d241076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24342, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24342, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24474 q = 1) (hb : d208034 q = 1) : d241154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24474, d241154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58973 q ha hb
    | true =>
      simp only [d24474, d241154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58972 q ha hb
  have h9 (q : Pattern) (ha : d24475 q = 1) (hb : d208034 q = 1) : d241155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24475, d241155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24475, d241155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24476 q = 1) (hb : d208034 q = 1) : d241156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24476, d241156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24476, d241156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24477 q = 1) (hb : d208034 q = 1) : d241157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24477, d241157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24477, d241157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24478 q = 1) (hb : d208034 q = 1) : d241158 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24478, d241158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24478, d241158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24479 q = 1) (hb : d208034 q = 1) : d241159 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24479, d241159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24479, d241159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58975 (p : Pattern) (ha : d24485 p = 1) (hb : d208034 p = 1) : d241165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24480 q = 1) (hb : d208034 q = 1) : d241160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24480, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58974 q ha hb
    | true =>
      simp only [d24480, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24481 q = 1) (hb : d208034 q = 1) : d241161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24481, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24481, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24482 q = 1) (hb : d208034 q = 1) : d241162 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24482, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24482, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24483 q = 1) (hb : d208034 q = 1) : d241163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24483, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24483, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24484 q = 1) (hb : d208034 q = 1) : d241164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24484, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24484, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24485 q = 1) (hb : d208034 q = 1) : d241165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24485, d241165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24485, d241165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58976 (p : Pattern) (ha : d208034 p = 1) (hb : d211286 p = 1) : d241171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24383 q = 1) (hb : d208034 q = 1) : d241117 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24383, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58963 q ha hb
    | true =>
      simp only [d24383, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58964 q ha hb
  have h2 (q : Pattern) (ha : d24384 q = 1) (hb : d208034 q = 1) : d241118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24384, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24384, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24385 q = 1) (hb : d208034 q = 1) : d241119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24385, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24385, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24386 q = 1) (hb : d208034 q = 1) : d241120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24386, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24386, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24393 q = 1) (hb : d208034 q = 1) : d241127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24393, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58965 q ha hb
    | true =>
      simp only [d24393, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58966 q ha hb
  have h6 (q : Pattern) (ha : d24394 q = 1) (hb : d208034 q = 1) : d241128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24394, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24394, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24395 q = 1) (hb : d208034 q = 1) : d241129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24395, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24395, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24417 q = 1) (hb : d208034 q = 1) : d241144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24417, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58970 q ha hb
    | true =>
      simp only [d24417, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58949 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211282 q = 1) : d241145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211282, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211282, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d24486 q = 1) (hb : d208034 q = 1) : d241166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24486, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58975 q ha hb
    | true =>
      simp only [d24486, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24487 q = 1) (hb : d208034 q = 1) : d241167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24487, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24487, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211283 q = 1) : d241168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211283, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211283, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211284 q = 1) : d241169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211284, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211284, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211285 q = 1) : d241170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211285, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211285, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211286 q = 1) : d241171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211286, d241171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211286, d241171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58977 (p : Pattern) (ha : d24492 p = 1) (hb : d208034 p = 1) : d241172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24353 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24353, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24379 q = 1) (hb : d208034 q = 1) : d241113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24379, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24379, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24492 q = 1) (hb : d208034 q = 1) : d241172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24492, d241172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24492, d241172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58978 (p : Pattern) (ha : d24493 p = 1) (hb : d208034 p = 1) : d241173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24357 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24357, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24381 q = 1) (hb : d208034 q = 1) : d241115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24381, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24381, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24493 q = 1) (hb : d208034 q = 1) : d241173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24493, d241173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24493, d241173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58979 (p : Pattern) (ha : d24498 p = 1) (hb : d208034 p = 1) : d241178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24387 q = 1) (hb : d208034 q = 1) : d241121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24387, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24387, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24388 q = 1) (hb : d208034 q = 1) : d241122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24388, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24388, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24498 q = 1) (hb : d208034 q = 1) : d241178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24498, d241178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24498, d241178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58980 (p : Pattern) (ha : d24499 p = 1) (hb : d208034 p = 1) : d241179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58948 q ha hb
    | true =>
      simp only [d24350, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24390 q = 1) (hb : d208034 q = 1) : d241124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24390, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24390, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24391 q = 1) (hb : d208034 q = 1) : d241125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24391, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24391, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24499 q = 1) (hb : d208034 q = 1) : d241179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24499, d241179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24499, d241179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58981 (p : Pattern) (ha : d24503 p = 1) (hb : d208034 p = 1) : d241183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24411 q = 1) (hb : d208034 q = 1) : d241138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24411, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58969 q ha hb
    | true =>
      simp only [d24411, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24412 q = 1) (hb : d208034 q = 1) : d241139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24412, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24412, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24346 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58947 q ha hb
    | true =>
      simp only [d24346, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24347 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24413 q = 1) (hb : d208034 q = 1) : d241140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24413, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24413, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24414 q = 1) (hb : d208034 q = 1) : d241141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24414, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24414, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24415 q = 1) (hb : d208034 q = 1) : d241142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24415, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24415, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24503 q = 1) (hb : d208034 q = 1) : d241183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24503, d241183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24503, d241183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58982 (p : Pattern) (ha : d24509 p = 1) (hb : d208034 p = 1) : d241186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24480 q = 1) (hb : d208034 q = 1) : d241160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24480, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58974 q ha hb
    | true =>
      simp only [d24480, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24481 q = 1) (hb : d208034 q = 1) : d241161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24481, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24481, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24482 q = 1) (hb : d208034 q = 1) : d241162 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24482, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24482, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24483 q = 1) (hb : d208034 q = 1) : d241163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24483, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24483, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24484 q = 1) (hb : d208034 q = 1) : d241164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24484, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24484, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24509 q = 1) (hb : d208034 q = 1) : d241186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24509, d241186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24509, d241186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58983 (p : Pattern) (ha : d208034 p = 1) (hb : d211291 p = 1) : d241192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24383 q = 1) (hb : d208034 q = 1) : d241117 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24383, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58963 q ha hb
    | true =>
      simp only [d24383, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58964 q ha hb
  have h2 (q : Pattern) (ha : d24384 q = 1) (hb : d208034 q = 1) : d241118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24384, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24384, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24385 q = 1) (hb : d208034 q = 1) : d241119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24385, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24385, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24386 q = 1) (hb : d208034 q = 1) : d241120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24386, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24386, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24393 q = 1) (hb : d208034 q = 1) : d241127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24393, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58965 q ha hb
    | true =>
      simp only [d24393, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58966 q ha hb
  have h6 (q : Pattern) (ha : d24394 q = 1) (hb : d208034 q = 1) : d241128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24394, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24394, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24395 q = 1) (hb : d208034 q = 1) : d241129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24395, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24395, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24417 q = 1) (hb : d208034 q = 1) : d241144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24417, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58970 q ha hb
    | true =>
      simp only [d24417, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58949 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211282 q = 1) : d241145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211282, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211282, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d24486 q = 1) (hb : d208034 q = 1) : d241166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24486, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58975 q ha hb
    | true =>
      simp only [d24486, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24487 q = 1) (hb : d208034 q = 1) : d241167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24487, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24487, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d211283 q = 1) : d241168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211283, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211283, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211284 q = 1) : d241169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211284, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211284, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211285 q = 1) : d241170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211285, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211285, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24494 q = 1) (hb : d208034 q = 1) : d241174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24494, d241174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58977 q ha hb
    | true =>
      simp only [d24494, d241174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58978 q ha hb
  have h16 (q : Pattern) (ha : d24495 q = 1) (hb : d208034 q = 1) : d241175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24495, d241175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24495, d241175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24496 q = 1) (hb : d208034 q = 1) : d241176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24496, d241176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24496, d241176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24497 q = 1) (hb : d208034 q = 1) : d241177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24497, d241177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24497, d241177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24500 q = 1) (hb : d208034 q = 1) : d241180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24500, d241180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58979 q ha hb
    | true =>
      simp only [d24500, d241180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58980 q ha hb
  have h20 (q : Pattern) (ha : d24501 q = 1) (hb : d208034 q = 1) : d241181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24501, d241181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24501, d241181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24502 q = 1) (hb : d208034 q = 1) : d241182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24502, d241182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d24502, d241182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d24504 q = 1) (hb : d208034 q = 1) : d241184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24504, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58981 q ha hb
    | true =>
      simp only [d24504, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58952 q ha hb
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211287 q = 1) : d241185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211287, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d211287, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d24510 q = 1) (hb : d208034 q = 1) : d241187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24510, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58982 q ha hb
    | true =>
      simp only [d24510, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d24511 q = 1) (hb : d208034 q = 1) : d241188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24511, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d24511, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d208034 q = 1) (hb : d211288 q = 1) : d241189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211288, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211288, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d208034 q = 1) (hb : d211289 q = 1) : d241190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211289, d241190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211289, d241190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d208034 q = 1) (hb : d211290 q = 1) : d241191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211290, d241191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d211290, d241191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d208034 q = 1) (hb : d211291 q = 1) : d241192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211291, d241192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211291, d241192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro58984 (p : Pattern) (ha : d208034 p = 1) (hb : d211298 p = 1) : d241212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24504 q = 1) (hb : d208034 q = 1) : d241184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24504, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58981 q ha hb
    | true =>
      simp only [d24504, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58952 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211287 q = 1) : d241185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211287, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211287, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d24510 q = 1) (hb : d208034 q = 1) : d241187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24510, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58982 q ha hb
    | true =>
      simp only [d24510, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24511 q = 1) (hb : d208034 q = 1) : d241188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24511, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24511, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211288 q = 1) : d241189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211288, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211288, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211296 q = 1) : d241210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211296, d241210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211296, d241210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211297 q = 1) : d241211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211297, d241211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211297, d241211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211298 q = 1) : d241212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211298, d241212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211298, d241212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58985 (p : Pattern) (ha : d24557 p = 1) (hb : d208034 p = 1) : d241221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24543 q = 1) (hb : d208034 q = 1) : d26834 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24543, d26834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24543, d26834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58967 q ha hb
  have h2 (q : Pattern) (ha : d24399 q = 1) (hb : d208034 q = 1) : d26653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24399, d26653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58967 q ha hb
    | true =>
      simp only [d24399, d26653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24544 q = 1) (hb : d208034 q = 1) : d26835 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24544, d26835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24544, d26835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24400 q = 1) (hb : d208034 q = 1) : d26654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24400, d26654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24400, d26654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24545 q = 1) (hb : d208034 q = 1) : d26836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24545, d26836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24545, d26836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24546 q = 1) (hb : d208034 q = 1) : d26837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24546, d26837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24546, d26837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24547 q = 1) (hb : d208034 q = 1) : d26843 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24547, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24547, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58941 q ha hb
  have h8 (q : Pattern) (ha : d24312 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58941 q ha hb
    | true =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24548 q = 1) (hb : d208034 q = 1) : d26844 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24548, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24548, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24313 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24549 q = 1) (hb : d208034 q = 1) : d26845 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24549, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24549, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24550 q = 1) (hb : d208034 q = 1) : d26846 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24550, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24550, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24551 q = 1) (hb : d208034 q = 1) : d241220 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24551, d241220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24551, d241220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24552 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
  have h15 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24553 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24554 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24555 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24556 q = 1) (hb : d208034 q = 1) : d26851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24556, d26851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24556, d26851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24557 q = 1) (hb : d208034 q = 1) : d241221 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24557, d241221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24557, d241221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58986 (p : Pattern) (ha : d24563 p = 1) (hb : d208034 p = 1) : d241227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24547 q = 1) (hb : d208034 q = 1) : d26843 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24547, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24547, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58941 q ha hb
  have h2 (q : Pattern) (ha : d24312 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58941 q ha hb
    | true =>
      simp only [d24312, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24548 q = 1) (hb : d208034 q = 1) : d26844 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24548, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24548, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24313 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24313, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24549 q = 1) (hb : d208034 q = 1) : d26845 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24549, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24549, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24550 q = 1) (hb : d208034 q = 1) : d26846 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24550, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24550, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24552 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
  have h8 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24553 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24554 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24555 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24556 q = 1) (hb : d208034 q = 1) : d26851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24556, d26851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24556, d26851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24558 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
  have h15 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24559 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24560 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24561 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24562 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24562, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24562, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24563 q = 1) (hb : d208034 q = 1) : d241227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24563, d241227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24563, d241227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58987 (p : Pattern) (ha : d24579 p = 1) (hb : d208034 p = 1) : d241243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24564 q = 1) (hb : d208034 q = 1) : d241228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24564, d241228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58985 q ha hb
    | true =>
      simp only [d24564, d241228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58986 q ha hb
  have h2 (q : Pattern) (ha : d24565 q = 1) (hb : d208034 q = 1) : d241229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24565, d241229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24565, d241229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24566 q = 1) (hb : d208034 q = 1) : d241230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24566, d241230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24566, d241230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24569 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24569, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58986 q ha hb
    | true =>
      simp only [d24569, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
  have h5 (q : Pattern) (ha : d24570 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24570, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24570, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24571 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24571, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24571, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24572 q = 1) (hb : d208034 q = 1) : d241236 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24572, d241236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24572, d241236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24574 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
    | true =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58959 q ha hb
  have h9 (q : Pattern) (ha : d24575 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24576 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24577 q = 1) (hb : d208034 q = 1) : d241241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24577, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24577, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24578 q = 1) (hb : d208034 q = 1) : d241242 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24578, d241242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24578, d241242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24579 q = 1) (hb : d208034 q = 1) : d241243 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24579, d241243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24579, d241243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58988 (p : Pattern) (ha : d24584 p = 1) (hb : d208034 p = 1) : d241248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24569 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24569, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58986 q ha hb
    | true =>
      simp only [d24569, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
  have h2 (q : Pattern) (ha : d24570 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24570, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24570, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24571 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24571, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24571, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24574 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
    | true =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58959 q ha hb
  have h5 (q : Pattern) (ha : d24575 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24576 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24577 q = 1) (hb : d208034 q = 1) : d241241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24577, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24577, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24582 q = 1) (hb : d208034 q = 1) : d241246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24582, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24582, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24583 q = 1) (hb : d208034 q = 1) : d241247 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24583, d241247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24583, d241247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24584 q = 1) (hb : d208034 q = 1) : d241248 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24584, d241248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24584, d241248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58989 (p : Pattern) (ha : d24590 p = 1) (hb : d208034 p = 1) : d241254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24580 q = 1) (hb : d208034 q = 1) : d241244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24580, d241244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58987 q ha hb
    | true =>
      simp only [d24580, d241244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24581 q = 1) (hb : d208034 q = 1) : d241245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24581, d241245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24581, d241245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24585 q = 1) (hb : d208034 q = 1) : d241249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24585, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58988 q ha hb
    | true =>
      simp only [d24585, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24586 q = 1) (hb : d208034 q = 1) : d241250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24586, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24586, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24587 q = 1) (hb : d208034 q = 1) : d241251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24587, d241251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24587, d241251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24588 q = 1) (hb : d208034 q = 1) : d241252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24588, d241252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24588, d241252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24589 q = 1) (hb : d208034 q = 1) : d241253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24589, d241253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24589, d241253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24590 q = 1) (hb : d208034 q = 1) : d241254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24590, d241254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24590, d241254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58990 (p : Pattern) (ha : d24598 p = 1) (hb : d208034 p = 1) : d241262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24585 q = 1) (hb : d208034 q = 1) : d241249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24585, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58988 q ha hb
    | true =>
      simp only [d24585, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24586 q = 1) (hb : d208034 q = 1) : d241250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24586, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24586, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24593 q = 1) (hb : d208034 q = 1) : d241257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24593, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58960 q ha hb
    | true =>
      simp only [d24593, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24594 q = 1) (hb : d208034 q = 1) : d241258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24594, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24594, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24595 q = 1) (hb : d208034 q = 1) : d241259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24595, d241259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24595, d241259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24596 q = 1) (hb : d208034 q = 1) : d241260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24596, d241260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24596, d241260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24597 q = 1) (hb : d208034 q = 1) : d241261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24597, d241261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24597, d241261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24598 q = 1) (hb : d208034 q = 1) : d241262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24598, d241262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24598, d241262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58991 (p : Pattern) (ha : d5680 p = 1) (hb : d208034 p = 1) : d241271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5674 q = 1) (hb : d208034 q = 1) : d241265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5674, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58971 q ha hb
  have h2 (q : Pattern) (ha : d5630 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58971 q ha hb
    | true =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5675 q = 1) (hb : d208034 q = 1) : d241266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5675, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5631 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5676 q = 1) (hb : d208034 q = 1) : d241267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5676, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5677 q = 1) (hb : d208034 q = 1) : d241268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5677, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5678 q = 1) (hb : d208034 q = 1) : d241269 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5678, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5680 q = 1) (hb : d208034 q = 1) : d241271 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5680, d241271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5680, d241271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58992 (p : Pattern) (ha : d24644 p = 1) (hb : d208034 p = 1) : d241270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24552 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
  have h2 (q : Pattern) (ha : d24319 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58942 q ha hb
    | true =>
      simp only [d24319, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24553 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24553, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24320 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24320, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24554 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24554, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24555 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24555, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24558 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
  have h8 (q : Pattern) (ha : d24327 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58943 q ha hb
    | true =>
      simp only [d24327, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24559 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24559, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24328 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24328, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24560 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24560, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24561 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24561, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24562 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24562, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24562, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5674 q = 1) (hb : d208034 q = 1) : d241265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5674, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58971 q ha hb
  have h15 (q : Pattern) (ha : d5630 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58971 q ha hb
    | true =>
      simp only [d5630, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5675 q = 1) (hb : d208034 q = 1) : d241266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5675, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5631 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5631, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5676 q = 1) (hb : d208034 q = 1) : d241267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5676, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5677 q = 1) (hb : d208034 q = 1) : d241268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5677, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5678 q = 1) (hb : d208034 q = 1) : d241269 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5678, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d24644 q = 1) (hb : d208034 q = 1) : d241270 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24644, d241270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24644, d241270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58993 (p : Pattern) (ha : d24650 p = 1) (hb : d208034 p = 1) : d241277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24569 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24569, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58986 q ha hb
    | true =>
      simp only [d24569, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
  have h2 (q : Pattern) (ha : d24570 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24570, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24570, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24571 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24571, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24571, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24574 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58958 q ha hb
    | true =>
      simp only [d24574, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58959 q ha hb
  have h5 (q : Pattern) (ha : d24575 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24576 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24577 q = 1) (hb : d208034 q = 1) : d241241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24577, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24577, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24645 q = 1) (hb : d208034 q = 1) : d241272 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24645, d241272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58992 q ha hb
    | true =>
      simp only [d24645, d241272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58991 q ha hb
  have h9 (q : Pattern) (ha : d24646 q = 1) (hb : d208034 q = 1) : d241273 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24646, d241273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24646, d241273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24647 q = 1) (hb : d208034 q = 1) : d241274 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24647, d241274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24647, d241274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24648 q = 1) (hb : d208034 q = 1) : d241275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24648, d241275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24648, d241275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24649 q = 1) (hb : d208034 q = 1) : d241276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24649, d241276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24649, d241276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24650 q = 1) (hb : d208034 q = 1) : d241277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24650, d241277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24650, d241277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58994 (p : Pattern) (ha : d24656 p = 1) (hb : d208034 p = 1) : d241283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24651 q = 1) (hb : d208034 q = 1) : d241278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24651, d241278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58993 q ha hb
    | true =>
      simp only [d24651, d241278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24652 q = 1) (hb : d208034 q = 1) : d241279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24652, d241279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24652, d241279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24653 q = 1) (hb : d208034 q = 1) : d241280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24653, d241280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24653, d241280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24654 q = 1) (hb : d208034 q = 1) : d241281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24654, d241281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24654, d241281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24655 q = 1) (hb : d208034 q = 1) : d241282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24655, d241282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24655, d241282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24656 q = 1) (hb : d208034 q = 1) : d241283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24656, d241283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24656, d241283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58995 (p : Pattern) (ha : d208034 p = 1) (hb : d211308 p = 1) : d241289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24599 q = 1) (hb : d208034 q = 1) : d241263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24599, d241263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58989 q ha hb
    | true =>
      simp only [d24599, d241263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58990 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211304 q = 1) : d241264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211304, d241264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211304, d241264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d24657 q = 1) (hb : d208034 q = 1) : d241284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24657, d241284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58994 q ha hb
    | true =>
      simp only [d24657, d241284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24658 q = 1) (hb : d208034 q = 1) : d241285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24658, d241285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24658, d241285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211305 q = 1) : d241286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211305, d241286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211305, d241286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211306 q = 1) : d241287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211306, d241287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211306, d241287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d211307 q = 1) : d241288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211307, d241288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211307, d241288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211308 q = 1) : d241289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211308, d241289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211308, d241289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58996 (p : Pattern) (ha : d208034 p = 1) (hb : d211314 p = 1) : d241306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24366 q = 1) (hb : d208034 q = 1) : d241100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24366, d241100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24366, d241100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58951 q ha hb
  have h2 (q : Pattern) (ha : d24367 q = 1) (hb : d208034 q = 1) : d241101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24367, d241101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24367, d241101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24376 q = 1) (hb : d208034 q = 1) : d241110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58951 q ha hb
    | true =>
      simp only [d24376, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58954 q ha hb
  have h4 (q : Pattern) (ha : d24377 q = 1) (hb : d208034 q = 1) : d241111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24377, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24378 q = 1) (hb : d208034 q = 1) : d241112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d24378, d241112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24378, d241112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211292 q = 1) : d241193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211292, d241193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58976 q ha hb
    | true =>
      simp only [d211292, d241193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58983 q ha hb
  have h7 (q : Pattern) (ha : d24529 q = 1) (hb : d208034 q = 1) : d241206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24529, d241206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58955 q ha hb
    | true =>
      simp only [d24529, d241206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58956 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d211293 q = 1) : d241207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211293, d241207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211293, d241207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d211294 q = 1) : d241208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211294, d241208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211294, d241208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d211295 q = 1) : d241209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211295, d241209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211295, d241209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d211299 q = 1) : d241213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211299, d241213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211299, d241213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58984 q ha hb
  have h12 (q : Pattern) (ha : d24538 q = 1) (hb : d208034 q = 1) : d241215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24538, d241215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24538, d241215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58957 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d211300 q = 1) : d241216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211300, d241216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211300, d241216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d211301 q = 1) : d241217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211301, d241217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211301, d241217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d211302 q = 1) : d241218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211302, d241218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211302, d241218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d211303 q = 1) : d241219 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211303, d241219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211303, d241219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208034 q = 1) (hb : d211309 q = 1) : d241290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211309, d241290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211309, d241290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58995 q ha hb
  have h18 (q : Pattern) (ha : d24674 q = 1) (hb : d208034 q = 1) : d241301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24674, d241301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24674, d241301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58962 q ha hb
  have h19 (q : Pattern) (ha : d208034 q = 1) (hb : d211310 q = 1) : d241302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211310, d241302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211310, d241302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d208034 q = 1) (hb : d211311 q = 1) : d241303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211311, d241303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211311, d241303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208034 q = 1) (hb : d211312 q = 1) : d241304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211312, d241304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211312, d241304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208034 q = 1) (hb : d211313 q = 1) : d241305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211313, d241305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211313, d241305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208034 q = 1) (hb : d211314 q = 1) : d241306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211314, d241306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211314, d241306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro58997 (p : Pattern) (ha : d208034 p = 1) (hb : d211320 p = 1) : d241312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d211315 q = 1) : d241307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211315, d241307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211315, d241307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58996 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d211316 q = 1) : d241308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211316, d241308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211316, d241308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d211317 q = 1) : d241309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211317, d241309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211317, d241309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d211318 q = 1) : d241310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211318, d241310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211318, d241310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d211319 q = 1) : d241311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211319, d241311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211319, d241311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d211320 q = 1) : d241312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211320, d241312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211320, d241312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58998 (p : Pattern) (ha : d24692 p = 1) (hb : d208034 p = 1) : d27014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2009 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2010 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2010, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2011 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, d208034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2011, d208034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2012 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2009 q = 1) : d2009 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2026 q = 1) (hb : d152852 q = 1) : d10349 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d24690 q = 1) (hb : d208034 q = 1) : d10350 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24690, d208034, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24690, d208034, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d24691 q = 1) (hb : d208034 q = 1) : d10351 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24691, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24691, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24692 q = 1) (hb : d208034 q = 1) : d27014 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24692, d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24692, d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58999 (p : Pattern) (ha : d24699 p = 1) (hb : d208034 p = 1) : d27019 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2009 q = 1) : d2009 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2026 q = 1) (hb : d152852 q = 1) : d10349 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24690 q = 1) (hb : d208034 q = 1) : d10350 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24690, d208034, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24690, d208034, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24691 q = 1) (hb : d208034 q = 1) : d10351 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24691, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24691, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2025 q = 1) : d2025 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2044 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2045 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d24697 q = 1) (hb : d208034 q = 1) : d5716 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24697, d208034, d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24697, d208034, d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d24698 q = 1) (hb : d208034 q = 1) : d5717 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24698, d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24698, d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d24699 q = 1) (hb : d208034 q = 1) : d27019 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24699, d27019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24699, d27019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
end NetHack.Soko22Hazard87
