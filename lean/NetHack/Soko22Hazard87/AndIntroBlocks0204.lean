import NetHack.Soko22Hazard87.AndIntroBlocks0203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro51000 (p : Pattern) (ha : d74355 p = 1) (hb : d210372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26558 q = 1) (hb : d74350 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d74350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26558, d74350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26559 q = 1) (hb : d74351 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d74351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26559, d74351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d26560 q = 1) (hb : d74352 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d74352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26560, d74352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d74354 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74355 q = 1) (hb : d210372 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d74355, d210372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74355, d210372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro51001 (p : Pattern) (ha : d74362 p = 1) (hb : d210458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74356 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51000 q ha hb
    | true =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74357 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74358 q = 1) (hb : d210375 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74358, d210375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74358, d210375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74359 q = 1) (hb : d210376 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74359, d210376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74359, d210376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74360 q = 1) (hb : d210379 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74360, d210379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74360, d210379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74362 q = 1) (hb : d210458 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74362, d210458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74362, d210458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51002 (p : Pattern) (ha : d209055 p = 1) (hb : d210380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22226 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
    | true =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22227 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22228 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22228, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22229 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22229, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208963 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
    | true =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208964 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208965 q = 1) (hb : d210375 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d208965, d210375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208965, d210375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208966 q = 1) (hb : d210376 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d208966, d210376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208966, d210376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208967 q = 1) (hb : d210377 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d208967, d210377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208967, d210377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74356 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51000 q ha hb
    | true =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74357 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74358 q = 1) (hb : d210375 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74358, d210375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74358, d210375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74359 q = 1) (hb : d210376 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74359, d210376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74359, d210376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74360 q = 1) (hb : d210379 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74360, d210379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74360, d210379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209055 q = 1) (hb : d210380 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209055, d210380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209055, d210380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51003 (p : Pattern) (ha : d209061 p = 1) (hb : d210464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208971 q = 1) (hb : d210381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208971, d210381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50982 q ha hb
    | true =>
      simp only [d208971, d210381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50983 q ha hb
  have h2 (q : Pattern) (ha : d208972 q = 1) (hb : d210382 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208972, d210382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208972, d210382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208973 q = 1) (hb : d210383 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208973, d210383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208973, d210383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208975 q = 1) (hb : d210385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d208975, d210385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50983 q ha hb
    | true =>
      simp only [d208975, d210385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50984 q ha hb
  have h5 (q : Pattern) (ha : d208976 q = 1) (hb : d210386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d208976, d210386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208976, d210386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208977 q = 1) (hb : d210387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d208977, d210387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208977, d210387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208978 q = 1) (hb : d210388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d208978, d210388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208978, d210388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209056 q = 1) (hb : d210459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209056, d210459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51002 q ha hb
    | true =>
      simp only [d209056, d210459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51001 q ha hb
  have h9 (q : Pattern) (ha : d209057 q = 1) (hb : d210460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209057, d210460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209057, d210460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209058 q = 1) (hb : d210461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209058, d210461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209058, d210461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209059 q = 1) (hb : d210462 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209059, d210462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209059, d210462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209060 q = 1) (hb : d210463 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209060, d210463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209060, d210463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209061 q = 1) (hb : d210464 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209061, d210464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209061, d210464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51004 (p : Pattern) (ha : d209067 p = 1) (hb : d210470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209062 q = 1) (hb : d210465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209062, d210465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51003 q ha hb
    | true =>
      simp only [d209062, d210465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209063 q = 1) (hb : d210466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209063, d210466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209063, d210466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209064 q = 1) (hb : d210467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209064, d210467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209064, d210467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209065 q = 1) (hb : d210468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209065, d210468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209065, d210468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209066 q = 1) (hb : d210469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209066, d210469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209066, d210469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209067 q = 1) (hb : d210470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209067, d210470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209067, d210470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51005 (p : Pattern) (ha : d209073 p = 1) (hb : d210476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209019 q = 1) (hb : d210429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209019, d210429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50993 q ha hb
    | true =>
      simp only [d209019, d210429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50994 q ha hb
  have h2 (q : Pattern) (ha : d209020 q = 1) (hb : d210430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209020, d210430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209020, d210430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209021 q = 1) (hb : d210431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209021, d210431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209021, d210431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209022 q = 1) (hb : d210432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209022, d210432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209022, d210432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209029 q = 1) (hb : d210439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209029, d210439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50995 q ha hb
    | true =>
      simp only [d209029, d210439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50996 q ha hb
  have h6 (q : Pattern) (ha : d209030 q = 1) (hb : d210440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209030, d210440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209030, d210440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209031 q = 1) (hb : d210441 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209031, d210441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209031, d210441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209053 q = 1) (hb : d210456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209053, d210456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50999 q ha hb
    | true =>
      simp only [d209053, d210456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50987 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209054 q = 1) (hb : d210457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d210457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209054, d210457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209068 q = 1) (hb : d210471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209068, d210471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51004 q ha hb
    | true =>
      simp only [d209068, d210471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209069 q = 1) (hb : d210472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209069, d210472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209069, d210472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209070 q = 1) (hb : d210473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d210473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209070, d210473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209071 q = 1) (hb : d210474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d210474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209071, d210474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209072 q = 1) (hb : d210475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d210475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209072, d210475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209073 q = 1) (hb : d210476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209073, d210476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209073, d210476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro51006 (p : Pattern) (ha : d209074 p = 1) (hb : d210477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d210392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d210392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50985 q ha hb
    | true =>
      simp only [d208982, d210392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d210393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d210393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d210393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d210396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50986 q ha hb
    | true =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d210397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d210398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d210398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d210398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208989 q = 1) (hb : d210399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208989, d210399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208989, d210399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209015 q = 1) (hb : d210425 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209015, d210425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209015, d210425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209074 q = 1) (hb : d210477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209074, d210477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209074, d210477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51007 (p : Pattern) (ha : d209075 p = 1) (hb : d210478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d210396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50986 q ha hb
    | true =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d210397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d210402 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d210402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d210402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208993 q = 1) (hb : d210403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d208993, d210403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208993, d210403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209017 q = 1) (hb : d210427 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209017, d210427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209017, d210427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209075 q = 1) (hb : d210478 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209075, d210478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209075, d210478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51008 (p : Pattern) (ha : d209080 p = 1) (hb : d210483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208982 q = 1) (hb : d210392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d210392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50985 q ha hb
    | true =>
      simp only [d208982, d210392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208983 q = 1) (hb : d210393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d210393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d210393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208986 q = 1) (hb : d210396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50986 q ha hb
    | true =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208987 q = 1) (hb : d210397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208988 q = 1) (hb : d210398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208988, d210398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208988, d210398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209023 q = 1) (hb : d210433 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209023, d210433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209023, d210433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209024 q = 1) (hb : d210434 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209024, d210434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209024, d210434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209080 q = 1) (hb : d210483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209080, d210483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209080, d210483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51009 (p : Pattern) (ha : d209081 p = 1) (hb : d210484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208986 q = 1) (hb : d210396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50986 q ha hb
    | true =>
      simp only [d208986, d210396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208987 q = 1) (hb : d210397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208987, d210397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208992 q = 1) (hb : d210402 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d208992, d210402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208992, d210402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209026 q = 1) (hb : d210436 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209026, d210436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209026, d210436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209027 q = 1) (hb : d210437 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209027, d210437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209027, d210437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209081 q = 1) (hb : d210484 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209081, d210484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209081, d210484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51010 (p : Pattern) (ha : d209085 p = 1) (hb : d210488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209047 q = 1) (hb : d210450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209047, d210450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50998 q ha hb
    | true =>
      simp only [d209047, d210450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209048 q = 1) (hb : d210451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209048, d210451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209048, d210451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208982 q = 1) (hb : d210392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d208982, d210392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50985 q ha hb
    | true =>
      simp only [d208982, d210392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208983 q = 1) (hb : d210393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d208983, d210393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208983, d210393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209049 q = 1) (hb : d210452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209049, d210452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209049, d210452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209050 q = 1) (hb : d210453 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209050, d210453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209050, d210453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209051 q = 1) (hb : d210454 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209051, d210454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209051, d210454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209085 q = 1) (hb : d210488 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209085, d210488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209085, d210488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51011 (p : Pattern) (ha : d209088 p = 1) (hb : d210491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209062 q = 1) (hb : d210465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209062, d210465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51003 q ha hb
    | true =>
      simp only [d209062, d210465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209063 q = 1) (hb : d210466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209063, d210466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209063, d210466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209064 q = 1) (hb : d210467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209064, d210467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209064, d210467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209065 q = 1) (hb : d210468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209065, d210468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209065, d210468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209066 q = 1) (hb : d210469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209066, d210469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209066, d210469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209088 q = 1) (hb : d210491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209088, d210491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209088, d210491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51012 (p : Pattern) (ha : d209094 p = 1) (hb : d210497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209019 q = 1) (hb : d210429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209019, d210429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50993 q ha hb
    | true =>
      simp only [d209019, d210429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50994 q ha hb
  have h2 (q : Pattern) (ha : d209020 q = 1) (hb : d210430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209020, d210430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209020, d210430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209021 q = 1) (hb : d210431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209021, d210431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209021, d210431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209022 q = 1) (hb : d210432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209022, d210432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209022, d210432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209029 q = 1) (hb : d210439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209029, d210439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50995 q ha hb
    | true =>
      simp only [d209029, d210439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50996 q ha hb
  have h6 (q : Pattern) (ha : d209030 q = 1) (hb : d210440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209030, d210440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209030, d210440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209031 q = 1) (hb : d210441 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209031, d210441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209031, d210441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209053 q = 1) (hb : d210456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209053, d210456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50999 q ha hb
    | true =>
      simp only [d209053, d210456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50987 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209054 q = 1) (hb : d210457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d210457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209054, d210457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209068 q = 1) (hb : d210471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209068, d210471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51004 q ha hb
    | true =>
      simp only [d209068, d210471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209069 q = 1) (hb : d210472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209069, d210472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209069, d210472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209070 q = 1) (hb : d210473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d210473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209070, d210473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209071 q = 1) (hb : d210474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d210474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209071, d210474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209072 q = 1) (hb : d210475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d210475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209072, d210475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209076 q = 1) (hb : d210479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209076, d210479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51006 q ha hb
    | true =>
      simp only [d209076, d210479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51007 q ha hb
  have h17 (q : Pattern) (ha : d209077 q = 1) (hb : d210480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209077, d210480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209077, d210480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209078 q = 1) (hb : d210481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209078, d210481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209078, d210481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d209079 q = 1) (hb : d210482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209079, d210482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209079, d210482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209082 q = 1) (hb : d210485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209082, d210485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51008 q ha hb
    | true =>
      simp only [d209082, d210485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51009 q ha hb
  have h21 (q : Pattern) (ha : d209083 q = 1) (hb : d210486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209083, d210486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209083, d210486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d209084 q = 1) (hb : d210487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209084, d210487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209084, d210487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209086 q = 1) (hb : d210489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209086, d210489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51010 q ha hb
    | true =>
      simp only [d209086, d210489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50990 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209087 q = 1) (hb : d210490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d210490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d209087, d210490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d209089 q = 1) (hb : d210492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209089, d210492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51011 q ha hb
    | true =>
      simp only [d209089, d210492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d209090 q = 1) (hb : d210493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209090, d210493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d209090, d210493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d209091 q = 1) (hb : d210494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d210494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209091, d210494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d209092 q = 1) (hb : d210495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209092, d210495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d209092, d210495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209093 q = 1) (hb : d210496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209093, d210496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209093, d210496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209094 q = 1) (hb : d210497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209094, d210497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209094, d210497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro51013 (p : Pattern) (ha : d209101 p = 1) (hb : d210504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208996 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50987 q ha hb
    | true =>
      simp only [d208996, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50988 q ha hb
  have h2 (q : Pattern) (ha : d208997 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208997, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208997, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208998 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208998, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208998, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208999 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208999, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208999, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209000 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209000, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209000, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209096 q = 1) (hb : d210499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209096, d210499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50988 q ha hb
    | true =>
      simp only [d209096, d210499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209097 q = 1) (hb : d210500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209097, d210500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209097, d210500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209098 q = 1) (hb : d210501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209098, d210501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209098, d210501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209099 q = 1) (hb : d210502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209099, d210502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209099, d210502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209100 q = 1) (hb : d210503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209100, d210503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209100, d210503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209101 q = 1) (hb : d210504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209101, d210504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209101, d210504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51014 (p : Pattern) (ha : d209107 p = 1) (hb : d210510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209096 q = 1) (hb : d210499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209096, d210499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50988 q ha hb
    | true =>
      simp only [d209096, d210499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209097 q = 1) (hb : d210500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209097, d210500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209097, d210500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209098 q = 1) (hb : d210501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209098, d210501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209098, d210501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209099 q = 1) (hb : d210502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209099, d210502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209099, d210502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209100 q = 1) (hb : d210503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209100, d210503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209100, d210503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209102 q = 1) (hb : d210505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209102, d210505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50991 q ha hb
    | true =>
      simp only [d209102, d210505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209103 q = 1) (hb : d210506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209103, d210506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209103, d210506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209104 q = 1) (hb : d210507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209104, d210507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209104, d210507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209105 q = 1) (hb : d210508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209105, d210508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209105, d210508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209106 q = 1) (hb : d210509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209106, d210509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209106, d210509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209107 q = 1) (hb : d210510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209107, d210510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209107, d210510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51015 (p : Pattern) (ha : d209114 p = 1) (hb : d210517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209086 q = 1) (hb : d210489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209086, d210489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51010 q ha hb
    | true =>
      simp only [d209086, d210489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50990 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209087 q = 1) (hb : d210490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d210490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209087, d210490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209089 q = 1) (hb : d210492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209089, d210492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51011 q ha hb
    | true =>
      simp only [d209089, d210492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209090 q = 1) (hb : d210493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209090, d210493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209090, d210493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209091 q = 1) (hb : d210494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d210494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209091, d210494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209112 q = 1) (hb : d210515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209112, d210515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209112, d210515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209113 q = 1) (hb : d210516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209113, d210516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209113, d210516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209114 q = 1) (hb : d210517 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d210517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d210517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51016 (p : Pattern) (ha : d209116 p = 1) (hb : d210519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209102 q = 1) (hb : d210505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209102, d210505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50991 q ha hb
    | true =>
      simp only [d209102, d210505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209103 q = 1) (hb : d210506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209103, d210506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209103, d210506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209104 q = 1) (hb : d210507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209104, d210507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209104, d210507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209105 q = 1) (hb : d210508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209105, d210508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209105, d210508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209106 q = 1) (hb : d210509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209106, d210509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209106, d210509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209116 q = 1) (hb : d210519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209116, d210519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209116, d210519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51017 (p : Pattern) (ha : d209136 p = 1) (hb : d210526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15380 q = 1) (hb : d209126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15380, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50979 q ha hb
  have h3 (q : Pattern) (ha : d10046 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50979 q ha hb
    | true =>
      simp only [d10046, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15381 q = 1) (hb : d209127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15381, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10048 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10048, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15382 q = 1) (hb : d209128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15382, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15383 q = 1) (hb : d209129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15383, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d209130 q = 1) (hb : d210525 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209130, d210525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209130, d210525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d22502 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
  have h10 (q : Pattern) (ha : d22226 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
    | true =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d22503 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22227 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d22504 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22505 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d22506 q = 1) (hb : d209135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22506, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22506, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209136 q = 1) (hb : d210526 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209136, d210526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209136, d210526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro51018 (p : Pattern) (ha : d209142 p = 1) (hb : d210532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15380 q = 1) (hb : d209126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50979 q ha hb
  have h2 (q : Pattern) (ha : d10046 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50979 q ha hb
    | true =>
      simp only [d10046, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15381 q = 1) (hb : d209127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15381, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10048 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10048, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15382 q = 1) (hb : d209128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15382, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15383 q = 1) (hb : d209129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15383, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22502 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
  have h8 (q : Pattern) (ha : d22226 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
    | true =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22503 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22227 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22504 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22505 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22506 q = 1) (hb : d209135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22506, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22506, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209137 q = 1) (hb : d210527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
  have h15 (q : Pattern) (ha : d208963 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
    | true =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209138 q = 1) (hb : d210528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208964 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d209139 q = 1) (hb : d210529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d209140 q = 1) (hb : d210530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d209141 q = 1) (hb : d210531 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209141, d210531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d209141, d210531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d209142 q = 1) (hb : d210532 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209142, d210532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d209142, d210532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro51019 (p : Pattern) (ha : d209147 p = 1) (hb : d210537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22502 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
  have h2 (q : Pattern) (ha : d22226 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
    | true =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22503 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22227 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22504 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22505 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209137 q = 1) (hb : d210527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
  have h8 (q : Pattern) (ha : d208963 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
    | true =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209138 q = 1) (hb : d210528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208964 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209139 q = 1) (hb : d210529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209140 q = 1) (hb : d210530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209141 q = 1) (hb : d210531 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209141, d210531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209141, d210531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209146 q = 1) (hb : d210536 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209146, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209146, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209147 q = 1) (hb : d210537 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209147, d210537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209147, d210537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51020 (p : Pattern) (ha : d209152 p = 1) (hb : d210542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209137 q = 1) (hb : d210527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
  have h2 (q : Pattern) (ha : d208963 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
    | true =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209138 q = 1) (hb : d210528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208964 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209139 q = 1) (hb : d210529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209140 q = 1) (hb : d210530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209146 q = 1) (hb : d210536 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209146, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209146, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1883 q = 1) (hb : d53209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
  have h9 (q : Pattern) (ha : d1597 q = 1) (hb : d53038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
    | true =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1884 q = 1) (hb : d53210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1598 q = 1) (hb : d53039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1885 q = 1) (hb : d53211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1886 q = 1) (hb : d53212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1887 q = 1) (hb : d53213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d209152 q = 1) (hb : d210542 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209152, d210542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209152, d210542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro51021 (p : Pattern) (ha : d209158 p = 1) (hb : d210548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209143 q = 1) (hb : d210533 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209143, d210533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51017 q ha hb
    | true =>
      simp only [d209143, d210533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51018 q ha hb
  have h2 (q : Pattern) (ha : d209144 q = 1) (hb : d210534 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209144, d210534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209144, d210534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209145 q = 1) (hb : d210535 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209145, d210535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209145, d210535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209148 q = 1) (hb : d210538 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209148, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51018 q ha hb
    | true =>
      simp only [d209148, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
  have h5 (q : Pattern) (ha : d209149 q = 1) (hb : d210539 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209149, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209149, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209150 q = 1) (hb : d210540 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209150, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209150, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209151 q = 1) (hb : d210541 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209151, d210541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209151, d210541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209153 q = 1) (hb : d210543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
    | true =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51020 q ha hb
  have h9 (q : Pattern) (ha : d209154 q = 1) (hb : d210544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209155 q = 1) (hb : d210545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209156 q = 1) (hb : d210546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209156, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209156, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209157 q = 1) (hb : d210547 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209157, d210547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209157, d210547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209158 q = 1) (hb : d210548 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209158, d210548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209158, d210548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51022 (p : Pattern) (ha : d209163 p = 1) (hb : d210553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209148 q = 1) (hb : d210538 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209148, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51018 q ha hb
    | true =>
      simp only [d209148, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
  have h2 (q : Pattern) (ha : d209149 q = 1) (hb : d210539 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209149, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209149, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209150 q = 1) (hb : d210540 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209150, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209150, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209153 q = 1) (hb : d210543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
    | true =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51020 q ha hb
  have h5 (q : Pattern) (ha : d209154 q = 1) (hb : d210544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209155 q = 1) (hb : d210545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209156 q = 1) (hb : d210546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209156, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209156, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209161 q = 1) (hb : d210551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209161, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209161, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209162 q = 1) (hb : d210552 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209162, d210552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209162, d210552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209163 q = 1) (hb : d210553 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209163, d210553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209163, d210553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro51023 (p : Pattern) (ha : d209169 p = 1) (hb : d210559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209159 q = 1) (hb : d210549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209159, d210549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51021 q ha hb
    | true =>
      simp only [d209159, d210549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209160 q = 1) (hb : d210550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209160, d210550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209160, d210550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209164 q = 1) (hb : d210554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209164, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51022 q ha hb
    | true =>
      simp only [d209164, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209165 q = 1) (hb : d210555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209165, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209165, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209166 q = 1) (hb : d210556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209166, d210556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209166, d210556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209167 q = 1) (hb : d210557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209167, d210557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209167, d210557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209168 q = 1) (hb : d210558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209168, d210558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209168, d210558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209169 q = 1) (hb : d210559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209169, d210559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209169, d210559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51024 (p : Pattern) (ha : d209171 p = 1) (hb : d210561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209153 q = 1) (hb : d210543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
    | true =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51020 q ha hb
  have h2 (q : Pattern) (ha : d209154 q = 1) (hb : d210544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209155 q = 1) (hb : d210545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209161 q = 1) (hb : d210551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209161, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209161, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209170 q = 1) (hb : d210560 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209170, d210560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209170, d210560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209171 q = 1) (hb : d210561 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209171, d210561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209171, d210561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51025 (p : Pattern) (ha : d209177 p = 1) (hb : d210567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209164 q = 1) (hb : d210554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209164, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51022 q ha hb
    | true =>
      simp only [d209164, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209165 q = 1) (hb : d210555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209165, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209165, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209172 q = 1) (hb : d210562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209172, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51024 q ha hb
    | true =>
      simp only [d209172, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209173 q = 1) (hb : d210563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209173, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209173, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209174 q = 1) (hb : d210564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209174, d210564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209174, d210564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209175 q = 1) (hb : d210565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209175, d210565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209175, d210565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209176 q = 1) (hb : d210566 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209176, d210566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209176, d210566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209177 q = 1) (hb : d210567 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209177, d210567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209177, d210567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51026 (p : Pattern) (ha : d74406 p = 1) (hb : d210570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74400 q = 1) (hb : d210527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74400, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74400, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51000 q ha hb
  have h2 (q : Pattern) (ha : d74356 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51000 q ha hb
    | true =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74401 q = 1) (hb : d210528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74401, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74401, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74357 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74402 q = 1) (hb : d210529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74402, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74402, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74403 q = 1) (hb : d210530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74403, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74403, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d74404 q = 1) (hb : d210536 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74404, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74404, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d74406 q = 1) (hb : d210570 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74406, d210570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74406, d210570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51027 (p : Pattern) (ha : d209185 p = 1) (hb : d210537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22502 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
  have h2 (q : Pattern) (ha : d22226 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50980 q ha hb
    | true =>
      simp only [d22226, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22503 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22503, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22227 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22227, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22504 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22504, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22505 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22505, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209137 q = 1) (hb : d210527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209137, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
  have h8 (q : Pattern) (ha : d208963 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50981 q ha hb
    | true =>
      simp only [d208963, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209138 q = 1) (hb : d210528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209138, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208964 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208964, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209139 q = 1) (hb : d210529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209139, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209140 q = 1) (hb : d210530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209140, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209141 q = 1) (hb : d210531 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209141, d210531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209141, d210531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74400 q = 1) (hb : d210527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74400, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74400, d210527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51000 q ha hb
  have h15 (q : Pattern) (ha : d74356 q = 1) (hb : d210373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51000 q ha hb
    | true =>
      simp only [d74356, d210373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74401 q = 1) (hb : d210528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74401, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74401, d210528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74357 q = 1) (hb : d210374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74357, d210374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74402 q = 1) (hb : d210529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74402, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74402, d210529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74403 q = 1) (hb : d210530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74403, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74403, d210530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74404 q = 1) (hb : d210536 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74404, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74404, d210536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209185 q = 1) (hb : d210537 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209185, d210537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209185, d210537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro51028 (p : Pattern) (ha : d209191 p = 1) (hb : d210576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209148 q = 1) (hb : d210538 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209148, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51018 q ha hb
    | true =>
      simp only [d209148, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
  have h2 (q : Pattern) (ha : d209149 q = 1) (hb : d210539 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209149, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209149, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209150 q = 1) (hb : d210540 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209150, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209150, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209153 q = 1) (hb : d210543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51019 q ha hb
    | true =>
      simp only [d209153, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51020 q ha hb
  have h5 (q : Pattern) (ha : d209154 q = 1) (hb : d210544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209154, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209155 q = 1) (hb : d210545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209155, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209156 q = 1) (hb : d210546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209156, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209156, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209186 q = 1) (hb : d210571 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209186, d210571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51027 q ha hb
    | true =>
      simp only [d209186, d210571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51026 q ha hb
  have h9 (q : Pattern) (ha : d209187 q = 1) (hb : d210572 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209187, d210572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209187, d210572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209188 q = 1) (hb : d210573 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209188, d210573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209188, d210573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209189 q = 1) (hb : d210574 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209189, d210574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209189, d210574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209190 q = 1) (hb : d210575 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209190, d210575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209190, d210575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209191 q = 1) (hb : d210576 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209191, d210576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209191, d210576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51029 (p : Pattern) (ha : d209197 p = 1) (hb : d210582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209192 q = 1) (hb : d210577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209192, d210577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51028 q ha hb
    | true =>
      simp only [d209192, d210577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209193 q = 1) (hb : d210578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209193, d210578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209193, d210578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209194 q = 1) (hb : d210579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209194, d210579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209194, d210579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209195 q = 1) (hb : d210580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209195, d210580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209195, d210580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209196 q = 1) (hb : d210581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209196, d210581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209196, d210581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209197 q = 1) (hb : d210582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209197, d210582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209197, d210582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51030 (p : Pattern) (ha : d209203 p = 1) (hb : d210588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209178 q = 1) (hb : d210568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209178, d210568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51023 q ha hb
    | true =>
      simp only [d209178, d210568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51025 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d210569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d210569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209184, d210569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209198 q = 1) (hb : d210583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209198, d210583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51029 q ha hb
    | true =>
      simp only [d209198, d210583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209199 q = 1) (hb : d210584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209199, d210584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209199, d210584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209200 q = 1) (hb : d210585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d210585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d210585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209201 q = 1) (hb : d210586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d210586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d210586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209202 q = 1) (hb : d210587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d210587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d210587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209203 q = 1) (hb : d210588 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d210588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d210588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51031 (p : Pattern) (ha : d209182 p = 1) (hb : d210593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209172 q = 1) (hb : d210562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209172, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51024 q ha hb
    | true =>
      simp only [d209172, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209173 q = 1) (hb : d210563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209173, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209173, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209179 q = 1) (hb : d210590 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209179, d210590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209179, d210590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209180 q = 1) (hb : d210591 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209180, d210591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209180, d210591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209181 q = 1) (hb : d210592 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209181, d210592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209181, d210592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209182 q = 1) (hb : d210593 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209182, d210593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209182, d210593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51032 (p : Pattern) (ha : d209210 p = 1) (hb : d210599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209205 q = 1) (hb : d210594 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209205, d210594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51031 q ha hb
    | true =>
      simp only [d209205, d210594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209206 q = 1) (hb : d210595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209206, d210595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209206, d210595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209207 q = 1) (hb : d210596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209207, d210596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209207, d210596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209208 q = 1) (hb : d210597 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209208, d210597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209208, d210597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209209 q = 1) (hb : d210598 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209209, d210598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209209, d210598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209210 q = 1) (hb : d210599 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209210, d210599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209210, d210599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51033 (p : Pattern) (ha : d209216 p = 1) (hb : d210605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209002 q = 1) (hb : d210412 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209002, d210412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209002, d210412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50989 q ha hb
  have h2 (q : Pattern) (ha : d209003 q = 1) (hb : d210413 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209003, d210413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209003, d210413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209012 q = 1) (hb : d210422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209012, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50989 q ha hb
    | true =>
      simp only [d209012, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50992 q ha hb
  have h4 (q : Pattern) (ha : d209013 q = 1) (hb : d210423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209013, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209013, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209014 q = 1) (hb : d210424 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209014, d210424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209014, d210424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209095 q = 1) (hb : d210498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209095, d210498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51005 q ha hb
    | true =>
      simp only [d209095, d210498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51012 q ha hb
  have h7 (q : Pattern) (ha : d209108 q = 1) (hb : d210511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209108, d210511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51013 q ha hb
    | true =>
      simp only [d209108, d210511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51014 q ha hb
  have h8 (q : Pattern) (ha : d209109 q = 1) (hb : d210512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209109, d210512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209109, d210512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209110 q = 1) (hb : d210513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d210513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209110, d210513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209111 q = 1) (hb : d210514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d210514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209111, d210514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209115 q = 1) (hb : d210518 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d210518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209115, d210518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51015 q ha hb
  have h12 (q : Pattern) (ha : d209117 q = 1) (hb : d210520 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209117, d210520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209117, d210520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51016 q ha hb
  have h13 (q : Pattern) (ha : d209118 q = 1) (hb : d210521 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d210521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209118, d210521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209119 q = 1) (hb : d210522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d210522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209119, d210522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209120 q = 1) (hb : d210523 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d210523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209120, d210523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209121 q = 1) (hb : d210524 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d210524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209121, d210524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209204 q = 1) (hb : d210589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d210589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209204, d210589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51030 q ha hb
  have h18 (q : Pattern) (ha : d209211 q = 1) (hb : d210600 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209211, d210600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209211, d210600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51032 q ha hb
  have h19 (q : Pattern) (ha : d209212 q = 1) (hb : d210601 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d210601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209212, d210601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209213 q = 1) (hb : d210602 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d210602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209213, d210602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209214 q = 1) (hb : d210603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d210603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209214, d210603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209215 q = 1) (hb : d210604 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d210604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209215, d210604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209216 q = 1) (hb : d210605 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d210605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209216, d210605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro51034 (p : Pattern) (ha : d209222 p = 1) (hb : d210611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d210606 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d210606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d210606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51033 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d210607 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d210607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d210607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d210608 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d210608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d210608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d210609 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d210609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d210609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d210610 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d210610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d210610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d210611 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d210611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d210611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51035 (p : Pattern) (ha : d10352 p = 1) (hb : d209236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10349 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10349, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10350 q = 1) (hb : d209227 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10350, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10351 q = 1) (hb : d209228 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10351, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209235 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10352 q = 1) (hb : d209236 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10352, d209236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10352, d209236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51036 (p : Pattern) (ha : d13677 p = 1) (hb : d209244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5716 q = 1) (hb : d209234 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5717 q = 1) (hb : d209235 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5717, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209243 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13677 q = 1) (hb : d209244 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d209244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13677, d209244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51037 (p : Pattern) (ha : d22772 p = 1) (hb : d209252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d209249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22693 q = 1) (hb : d209251 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22693, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22772 q = 1) (hb : d209252 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22772, d209252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22772, d209252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51038 (p : Pattern) (ha : d201470 p = 1) (hb : d209250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13675 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13676 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17228 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17228, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d13680 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13681 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d13682 q = 1) (hb : d209249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13682, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d201470 q = 1) (hb : d209250 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d201470, d209250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201470, d209250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro51039 (p : Pattern) (ha : d209256 p = 1) (hb : d210616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13680 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13681 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22693 q = 1) (hb : d209251 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22693, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2082 q = 1) (hb : d53361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2083 q = 1) (hb : d53362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2084 q = 1) (hb : d53363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d209256 q = 1) (hb : d210616 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209256, d210616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d209256, d210616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro51040 (p : Pattern) (ha : d209263 p = 1) (hb : d210623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201543 q = 1) (hb : d209253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201543, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51038 q ha hb
    | true =>
      simp only [d201543, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q ha hb
  have h2 (q : Pattern) (ha : d201544 q = 1) (hb : d209254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201544, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201544, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201545 q = 1) (hb : d209255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201545, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201545, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209257 q = 1) (hb : d210617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q hb ha
    | true =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51039 q ha hb
  have h5 (q : Pattern) (ha : d209258 q = 1) (hb : d210618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209259 q = 1) (hb : d210619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209260 q = 1) (hb : d210620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d210620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209260, d210620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209261 q = 1) (hb : d210621 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209261, d210621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209261, d210621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209262 q = 1) (hb : d210622 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209262, d210622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209262, d210622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209263 q = 1) (hb : d210623 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209263, d210623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209263, d210623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro51041 (p : Pattern) (ha : d209267 p = 1) (hb : d210627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209257 q = 1) (hb : d210617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q hb ha
    | true =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51039 q ha hb
  have h2 (q : Pattern) (ha : d209258 q = 1) (hb : d210618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209259 q = 1) (hb : d210619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209261 q = 1) (hb : d210621 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209261, d210621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209261, d210621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209266 q = 1) (hb : d210626 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209266, d210626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209266, d210626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209267 q = 1) (hb : d210627 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209267, d210627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209267, d210627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51042 (p : Pattern) (ha : d209273 p = 1) (hb : d210633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d210630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d210631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209272 q = 1) (hb : d210632 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209272, d210632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209272, d210632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209273 q = 1) (hb : d210633 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209273, d210633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209273, d210633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51043 (p : Pattern) (ha : d209277 p = 1) (hb : d210637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d210634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d210635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209276 q = 1) (hb : d210636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209276, d210636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209276, d210636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209277 q = 1) (hb : d210637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209277, d210637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209277, d210637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51044 (p : Pattern) (ha : d209283 p = 1) (hb : d210643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
    | true =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209283 q = 1) (hb : d210643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209283, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209283, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51045 (p : Pattern) (ha : d209286 p = 1) (hb : d210646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d210630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d210631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209272 q = 1) (hb : d210632 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209272, d210632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209272, d210632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209286 q = 1) (hb : d210646 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209286, d210646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209286, d210646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51046 (p : Pattern) (ha : d209287 p = 1) (hb : d210647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d210634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d210635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209276 q = 1) (hb : d210636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209276, d210636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209276, d210636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209287 q = 1) (hb : d210647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209287, d210647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209287, d210647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51047 (p : Pattern) (ha : d209293 p = 1) (hb : d210653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
    | true =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209288 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51045 q ha hb
    | true =>
      simp only [d209288, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51046 q ha hb
  have h7 (q : Pattern) (ha : d209289 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209289, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209289, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209290 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209290, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209290, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209291 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209291, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209291, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209292 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209292, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209292, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209293 q = 1) (hb : d210653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209293, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209293, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51048 (p : Pattern) (ha : d209298 p = 1) (hb : d210658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d210630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d210631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209297 q = 1) (hb : d210657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209297, d210657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209297, d210657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209298 q = 1) (hb : d210658 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209298, d210658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209298, d210658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51049 (p : Pattern) (ha : d209300 p = 1) (hb : d210660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d210634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d210635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209299 q = 1) (hb : d210659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209299, d210659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209299, d210659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209300 q = 1) (hb : d210660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209300, d210660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209300, d210660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51050 (p : Pattern) (ha : d209307 p = 1) (hb : d210667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d210630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209305 q = 1) (hb : d210665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209305, d210665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209305, d210665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209306 q = 1) (hb : d210666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209306, d210666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209306, d210666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209307 q = 1) (hb : d210667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209307, d210667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209307, d210667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51051 (p : Pattern) (ha : d209310 p = 1) (hb : d210670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d210634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209308 q = 1) (hb : d210668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209308, d210668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209308, d210668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209309 q = 1) (hb : d210669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209309, d210669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209309, d210669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209310 q = 1) (hb : d210670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209310, d210670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209310, d210670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51052 (p : Pattern) (ha : d196934 p = 1) (hb : d209315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d13675 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13676 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d17228 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17228, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196934 q = 1) (hb : d209315 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196934, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196934, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51053 (p : Pattern) (ha : d209321 p = 1) (hb : d210675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201540 q = 1) (hb : d209316 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201540, d209316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51052 q ha hb
    | true =>
      simp only [d201540, d209316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51038 q ha hb
  have h2 (q : Pattern) (ha : d201541 q = 1) (hb : d209317 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201541, d209317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201541, d209317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201542 q = 1) (hb : d209318 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201542, d209318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201542, d209318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201543 q = 1) (hb : d209253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201543, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51038 q ha hb
    | true =>
      simp only [d201543, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q ha hb
  have h5 (q : Pattern) (ha : d201544 q = 1) (hb : d209254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201544, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201544, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201545 q = 1) (hb : d209255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201545, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201545, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201546 q = 1) (hb : d209319 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d201546, d209319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201546, d209319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209257 q = 1) (hb : d210617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q hb ha
    | true =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51039 q ha hb
  have h9 (q : Pattern) (ha : d209258 q = 1) (hb : d210618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209259 q = 1) (hb : d210619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209260 q = 1) (hb : d210620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d210620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209260, d210620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209320 q = 1) (hb : d210674 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209320, d210674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209320, d210674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209321 q = 1) (hb : d210675 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209321, d210675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209321, d210675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51054 (p : Pattern) (ha : d209327 p = 1) (hb : d210681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209322 q = 1) (hb : d210676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209322, d210676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51053 q ha hb
    | true =>
      simp only [d209322, d210676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209323 q = 1) (hb : d210677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209323, d210677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209323, d210677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209324 q = 1) (hb : d210678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209324, d210678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209324, d210678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209325 q = 1) (hb : d210679 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209325, d210679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209325, d210679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209326 q = 1) (hb : d210680 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209326, d210680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209326, d210680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209327 q = 1) (hb : d210681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209327, d210681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209327, d210681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51055 (p : Pattern) (ha : d13677 p = 1) (hb : d74446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d74445 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13677 q = 1) (hb : d74446 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d74446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13677, d74446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51056 (p : Pattern) (ha : d22772 p = 1) (hb : d209330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d209249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13678 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51055 q ha hb
    | true =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13679 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13680 q = 1) (hb : d74449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13681 q = 1) (hb : d74450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13681, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22693 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22693, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22772 q = 1) (hb : d209330 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22772, d209330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22772, d209330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51057 (p : Pattern) (ha : d74453 p = 1) (hb : d210684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13678 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51055 q ha hb
    | true =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13679 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13680 q = 1) (hb : d74449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13681 q = 1) (hb : d74450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13681, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22693 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22693, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74453 q = 1) (hb : d210684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74453, d210684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74453, d210684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51058 (p : Pattern) (ha : d209336 p = 1) (hb : d210690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201543 q = 1) (hb : d209253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201543, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51038 q ha hb
    | true =>
      simp only [d201543, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q ha hb
  have h2 (q : Pattern) (ha : d201544 q = 1) (hb : d209254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201544, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201544, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201545 q = 1) (hb : d209255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201545, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201545, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209257 q = 1) (hb : d210617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51037 q hb ha
    | true =>
      simp only [d209257, d210617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51039 q ha hb
  have h5 (q : Pattern) (ha : d209258 q = 1) (hb : d210618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d210618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209259 q = 1) (hb : d210619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d210619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209260 q = 1) (hb : d210620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d210620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209260, d210620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209331 q = 1) (hb : d210685 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209331, d210685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51056 q hb ha
    | true =>
      simp only [d209331, d210685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51057 q ha hb
  have h9 (q : Pattern) (ha : d209332 q = 1) (hb : d210686 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209332, d210686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209332, d210686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209333 q = 1) (hb : d210687 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209333, d210687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209333, d210687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209334 q = 1) (hb : d210688 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209334, d210688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209334, d210688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209335 q = 1) (hb : d210689 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209335, d210689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209335, d210689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209336 q = 1) (hb : d210690 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209336, d210690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209336, d210690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51059 (p : Pattern) (ha : d209342 p = 1) (hb : d210696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209337 q = 1) (hb : d210691 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209337, d210691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51058 q ha hb
    | true =>
      simp only [d209337, d210691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209338 q = 1) (hb : d210692 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209338, d210692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209338, d210692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209339 q = 1) (hb : d210693 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209339, d210693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209339, d210693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209340 q = 1) (hb : d210694 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209340, d210694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209340, d210694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209341 q = 1) (hb : d210695 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209341, d210695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209341, d210695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209342 q = 1) (hb : d210696 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209342, d210696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209342, d210696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51060 (p : Pattern) (ha : d209348 p = 1) (hb : d210702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209301 q = 1) (hb : d210661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209301, d210661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51048 q ha hb
    | true =>
      simp only [d209301, d210661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51049 q ha hb
  have h2 (q : Pattern) (ha : d209302 q = 1) (hb : d210662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209302, d210662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209302, d210662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209303 q = 1) (hb : d210663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209303, d210663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209303, d210663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209304 q = 1) (hb : d210664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209304, d210664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209304, d210664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209311 q = 1) (hb : d210671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209311, d210671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51050 q ha hb
    | true =>
      simp only [d209311, d210671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51051 q ha hb
  have h6 (q : Pattern) (ha : d209312 q = 1) (hb : d210672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209312, d210672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209312, d210672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209313 q = 1) (hb : d210673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209313, d210673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209313, d210673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209328 q = 1) (hb : d210682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209328, d210682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51054 q ha hb
    | true =>
      simp only [d209328, d210682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d210683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d210683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209329, d210683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209343 q = 1) (hb : d210697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209343, d210697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51059 q ha hb
    | true =>
      simp only [d209343, d210697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209344 q = 1) (hb : d210698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209344, d210698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209344, d210698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d210699 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d210699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d210699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d210700 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d210700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209346, d210700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d210701 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d210701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209347, d210701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209348 q = 1) (hb : d210702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d210702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d210702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro51061 (p : Pattern) (ha : d209349 p = 1) (hb : d210703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d210630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d210631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d210631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209297 q = 1) (hb : d210657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209297, d210657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209297, d210657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209349 q = 1) (hb : d210703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209349, d210703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209349, d210703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51062 (p : Pattern) (ha : d209350 p = 1) (hb : d210704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d210634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d210635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d210635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209299 q = 1) (hb : d210659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209299, d210659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209299, d210659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209350 q = 1) (hb : d210704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209350, d210704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209350, d210704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51063 (p : Pattern) (ha : d209355 p = 1) (hb : d210709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d210630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d210630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209305 q = 1) (hb : d210665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209305, d210665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209305, d210665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209306 q = 1) (hb : d210666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209306, d210666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209306, d210666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209355 q = 1) (hb : d210709 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209355, d210709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209355, d210709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51064 (p : Pattern) (ha : d209356 p = 1) (hb : d210710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d210628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51041 q ha hb
    | true =>
      simp only [d209268, d210628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d210629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d210629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d210634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d210634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209308 q = 1) (hb : d210668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209308, d210668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209308, d210668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209309 q = 1) (hb : d210669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209309, d210669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209309, d210669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209356 q = 1) (hb : d210710 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209356, d210710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209356, d210710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51065 (p : Pattern) (ha : d209360 p = 1) (hb : d210714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209322 q = 1) (hb : d210676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209322, d210676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51053 q ha hb
    | true =>
      simp only [d209322, d210676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209323 q = 1) (hb : d210677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209323, d210677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209323, d210677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209264 q = 1) (hb : d210624 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51040 q ha hb
    | true =>
      simp only [d209264, d210624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209265 q = 1) (hb : d210625 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d210625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209324 q = 1) (hb : d210678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209324, d210678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209324, d210678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209325 q = 1) (hb : d210679 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209325, d210679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209325, d210679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209326 q = 1) (hb : d210680 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209326, d210680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209326, d210680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209360 q = 1) (hb : d210714 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209360, d210714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209360, d210714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51066 (p : Pattern) (ha : d209363 p = 1) (hb : d210717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209337 q = 1) (hb : d210691 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209337, d210691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51058 q ha hb
    | true =>
      simp only [d209337, d210691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209338 q = 1) (hb : d210692 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209338, d210692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209338, d210692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209339 q = 1) (hb : d210693 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209339, d210693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209339, d210693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209340 q = 1) (hb : d210694 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209340, d210694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209340, d210694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209341 q = 1) (hb : d210695 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209341, d210695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209341, d210695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209363 q = 1) (hb : d210717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209363, d210717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209363, d210717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51067 (p : Pattern) (ha : d209369 p = 1) (hb : d210723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209301 q = 1) (hb : d210661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209301, d210661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51048 q ha hb
    | true =>
      simp only [d209301, d210661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51049 q ha hb
  have h2 (q : Pattern) (ha : d209302 q = 1) (hb : d210662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209302, d210662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209302, d210662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209303 q = 1) (hb : d210663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209303, d210663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209303, d210663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209304 q = 1) (hb : d210664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209304, d210664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209304, d210664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209311 q = 1) (hb : d210671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209311, d210671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51050 q ha hb
    | true =>
      simp only [d209311, d210671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51051 q ha hb
  have h6 (q : Pattern) (ha : d209312 q = 1) (hb : d210672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209312, d210672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209312, d210672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209313 q = 1) (hb : d210673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209313, d210673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209313, d210673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209328 q = 1) (hb : d210682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209328, d210682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51054 q ha hb
    | true =>
      simp only [d209328, d210682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d210683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d210683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209329, d210683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209343 q = 1) (hb : d210697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209343, d210697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51059 q ha hb
    | true =>
      simp only [d209343, d210697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209344 q = 1) (hb : d210698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209344, d210698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209344, d210698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d210699 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d210699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d210699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d210700 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d210700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209346, d210700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d210701 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d210701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209347, d210701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209351 q = 1) (hb : d210705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209351, d210705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51061 q ha hb
    | true =>
      simp only [d209351, d210705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51062 q ha hb
  have h17 (q : Pattern) (ha : d209352 q = 1) (hb : d210706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209352, d210706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209352, d210706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209353 q = 1) (hb : d210707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209353, d210707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209353, d210707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d209354 q = 1) (hb : d210708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209354, d210708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209354, d210708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209357 q = 1) (hb : d210711 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209357, d210711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51063 q ha hb
    | true =>
      simp only [d209357, d210711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51064 q ha hb
  have h21 (q : Pattern) (ha : d209358 q = 1) (hb : d210712 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209358, d210712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209358, d210712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d209359 q = 1) (hb : d210713 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209359, d210713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209359, d210713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209361 q = 1) (hb : d210715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209361, d210715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51065 q ha hb
    | true =>
      simp only [d209361, d210715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51045 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209362 q = 1) (hb : d210716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d210716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d209362, d210716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d209364 q = 1) (hb : d210718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209364, d210718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51066 q ha hb
    | true =>
      simp only [d209364, d210718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d209365 q = 1) (hb : d210719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209365, d210719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d209365, d210719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d209366 q = 1) (hb : d210720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d210720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209366, d210720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d209367 q = 1) (hb : d210721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d210721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d209367, d210721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209368 q = 1) (hb : d210722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d210722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209368, d210722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209369 q = 1) (hb : d210723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d210723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209369, d210723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro51068 (p : Pattern) (ha : d209376 p = 1) (hb : d210730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
    | true =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209371 q = 1) (hb : d210725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209371, d210725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
    | true =>
      simp only [d209371, d210725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209372 q = 1) (hb : d210726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209372, d210726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209372, d210726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209373 q = 1) (hb : d210727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209373, d210727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209373, d210727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209374 q = 1) (hb : d210728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209374, d210728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209374, d210728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209375 q = 1) (hb : d210729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209375, d210729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209375, d210729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209376 q = 1) (hb : d210730 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209376, d210730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209376, d210730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51069 (p : Pattern) (ha : d209382 p = 1) (hb : d210736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209371 q = 1) (hb : d210725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209371, d210725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
    | true =>
      simp only [d209371, d210725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209372 q = 1) (hb : d210726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209372, d210726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209372, d210726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209373 q = 1) (hb : d210727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209373, d210727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209373, d210727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209374 q = 1) (hb : d210728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209374, d210728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209374, d210728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209375 q = 1) (hb : d210729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209375, d210729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209375, d210729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209377 q = 1) (hb : d210731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209377, d210731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51046 q ha hb
    | true =>
      simp only [d209377, d210731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209378 q = 1) (hb : d210732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209378, d210732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209378, d210732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209379 q = 1) (hb : d210733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209379, d210733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209379, d210733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209380 q = 1) (hb : d210734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209380, d210734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209380, d210734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209381 q = 1) (hb : d210735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209381, d210735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209381, d210735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209382 q = 1) (hb : d210736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209382, d210736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209382, d210736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51070 (p : Pattern) (ha : d209389 p = 1) (hb : d210743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209361 q = 1) (hb : d210715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209361, d210715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51065 q ha hb
    | true =>
      simp only [d209361, d210715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51045 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d210716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d210716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209362, d210716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209364 q = 1) (hb : d210718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209364, d210718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51066 q ha hb
    | true =>
      simp only [d209364, d210718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209365 q = 1) (hb : d210719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209365, d210719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209365, d210719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209366 q = 1) (hb : d210720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d210720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d210720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209387 q = 1) (hb : d210741 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d210741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d210741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209388 q = 1) (hb : d210742 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d210742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d210742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209389 q = 1) (hb : d210743 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d210743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d210743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51071 (p : Pattern) (ha : d209391 p = 1) (hb : d210745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209377 q = 1) (hb : d210731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209377, d210731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51046 q ha hb
    | true =>
      simp only [d209377, d210731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209378 q = 1) (hb : d210732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209378, d210732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209378, d210732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209379 q = 1) (hb : d210733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209379, d210733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209379, d210733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209380 q = 1) (hb : d210734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209380, d210734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209380, d210734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209381 q = 1) (hb : d210735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209381, d210735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209381, d210735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209391 q = 1) (hb : d210745 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209391, d210745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209391, d210745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51072 (p : Pattern) (ha : d22938 p = 1) (hb : d209418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d209412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22937 q = 1) (hb : d209417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22937, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22938 q = 1) (hb : d209418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22938, d209418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22938, d209418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51073 (p : Pattern) (ha : d197015 p = 1) (hb : d209407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13813 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
  have h4 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d13814 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d13815 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13816 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d17374 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17374, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d197015 q = 1) (hb : d209407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d197015, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d197015, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51074 (p : Pattern) (ha : d201624 p = 1) (hb : d209413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13814 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13815 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13816 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17374 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17374, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13817 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
  have h10 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d13818 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d13819 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13820 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d13821 q = 1) (hb : d209412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13821, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201624 q = 1) (hb : d209413 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d201624, d209413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201624, d209413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro51075 (p : Pattern) (ha : d209423 p = 1) (hb : d210751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13817 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
  have h2 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13818 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13819 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13820 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22937 q = 1) (hb : d209417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22937, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2361 q = 1) (hb : d53526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
  have h9 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2362 q = 1) (hb : d53527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2363 q = 1) (hb : d53528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2364 q = 1) (hb : d53529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2365 q = 1) (hb : d53530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d209423 q = 1) (hb : d210751 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209423, d210751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209423, d210751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro51076 (p : Pattern) (ha : d209429 p = 1) (hb : d210757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201625 q = 1) (hb : d209414 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201625, d209414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51073 q ha hb
    | true =>
      simp only [d201625, d209414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51074 q ha hb
  have h2 (q : Pattern) (ha : d201626 q = 1) (hb : d209415 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201626, d209415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201626, d209415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201627 q = 1) (hb : d209416 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201627, d209416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201627, d209416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201628 q = 1) (hb : d209419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201628, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51074 q ha hb
    | true =>
      simp only [d201628, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q ha hb
  have h5 (q : Pattern) (ha : d201629 q = 1) (hb : d209420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201629, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201629, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201630 q = 1) (hb : d209421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201630, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201630, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201631 q = 1) (hb : d209422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d201631, d209422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201631, d209422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209424 q = 1) (hb : d210752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q hb ha
    | true =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51075 q ha hb
  have h9 (q : Pattern) (ha : d209425 q = 1) (hb : d210753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209426 q = 1) (hb : d210754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209427 q = 1) (hb : d210755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209427, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209428 q = 1) (hb : d210756 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209428, d210756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209428, d210756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209429 q = 1) (hb : d210757 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209429, d210757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209429, d210757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51077 (p : Pattern) (ha : d209434 p = 1) (hb : d210762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201628 q = 1) (hb : d209419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201628, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51074 q ha hb
    | true =>
      simp only [d201628, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q ha hb
  have h2 (q : Pattern) (ha : d201629 q = 1) (hb : d209420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201629, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201629, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201630 q = 1) (hb : d209421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201630, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201630, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209424 q = 1) (hb : d210752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q hb ha
    | true =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51075 q ha hb
  have h5 (q : Pattern) (ha : d209425 q = 1) (hb : d210753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209426 q = 1) (hb : d210754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209427 q = 1) (hb : d210755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209427, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209432 q = 1) (hb : d210760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209432, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209432, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209433 q = 1) (hb : d210761 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209433, d210761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209433, d210761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209434 q = 1) (hb : d210762 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209434, d210762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209434, d210762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro51078 (p : Pattern) (ha : d209440 p = 1) (hb : d210768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209430 q = 1) (hb : d210758 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209430, d210758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51076 q ha hb
    | true =>
      simp only [d209430, d210758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209431 q = 1) (hb : d210759 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209431, d210759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209431, d210759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209435 q = 1) (hb : d210763 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209435, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51077 q ha hb
    | true =>
      simp only [d209435, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209436 q = 1) (hb : d210764 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209436, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209436, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209437 q = 1) (hb : d210765 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209437, d210765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209437, d210765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209438 q = 1) (hb : d210766 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209438, d210766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209438, d210766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209439 q = 1) (hb : d210767 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209439, d210767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209439, d210767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209440 q = 1) (hb : d210768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209440, d210768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209440, d210768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51079 (p : Pattern) (ha : d209442 p = 1) (hb : d210770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209424 q = 1) (hb : d210752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q hb ha
    | true =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51075 q ha hb
  have h2 (q : Pattern) (ha : d209425 q = 1) (hb : d210753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209426 q = 1) (hb : d210754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209432 q = 1) (hb : d210760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209432, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209432, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209441 q = 1) (hb : d210769 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209441, d210769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209441, d210769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209442 q = 1) (hb : d210770 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209442, d210770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209442, d210770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51080 (p : Pattern) (ha : d209448 p = 1) (hb : d210776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209435 q = 1) (hb : d210763 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209435, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51077 q ha hb
    | true =>
      simp only [d209435, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209436 q = 1) (hb : d210764 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209436, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209436, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209443 q = 1) (hb : d210771 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209443, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51079 q ha hb
    | true =>
      simp only [d209443, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209444 q = 1) (hb : d210772 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209444, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209444, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209445 q = 1) (hb : d210773 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209445, d210773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209445, d210773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209446 q = 1) (hb : d210774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209446, d210774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209446, d210774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209447 q = 1) (hb : d210775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209447, d210775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209447, d210775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209448 q = 1) (hb : d210776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209448, d210776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209448, d210776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51081 (p : Pattern) (ha : d22938 p = 1) (hb : d209456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51035 q ha hb
    | true =>
      simp only [d10353, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51036 q ha hb
    | true =>
      simp only [d13678, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d209412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13817 q = 1) (hb : d74491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51055 q ha hb
  have h15 (q : Pattern) (ha : d13678 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51055 q ha hb
    | true =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13818 q = 1) (hb : d74492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13818, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13679 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13819 q = 1) (hb : d74493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13819, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13820 q = 1) (hb : d74494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13820, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d22937 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22937, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d22938 q = 1) (hb : d209456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22938, d209456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22938, d209456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro51082 (p : Pattern) (ha : d74497 p = 1) (hb : d210779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13817 q = 1) (hb : d74491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51055 q ha hb
  have h2 (q : Pattern) (ha : d13678 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51055 q ha hb
    | true =>
      simp only [d13678, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13818 q = 1) (hb : d74492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13818, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13679 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13679, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13819 q = 1) (hb : d74493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13819, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13820 q = 1) (hb : d74494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13820, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22937 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22937, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d74497 q = 1) (hb : d210779 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74497, d210779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74497, d210779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51083 (p : Pattern) (ha : d209462 p = 1) (hb : d210785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201628 q = 1) (hb : d209419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d201628, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51074 q ha hb
    | true =>
      simp only [d201628, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q ha hb
  have h2 (q : Pattern) (ha : d201629 q = 1) (hb : d209420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d201629, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201629, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201630 q = 1) (hb : d209421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d201630, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201630, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209424 q = 1) (hb : d210752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51072 q hb ha
    | true =>
      simp only [d209424, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51075 q ha hb
  have h5 (q : Pattern) (ha : d209425 q = 1) (hb : d210753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209426 q = 1) (hb : d210754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209427 q = 1) (hb : d210755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209427, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209457 q = 1) (hb : d210780 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209457, d210780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51081 q hb ha
    | true =>
      simp only [d209457, d210780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51082 q ha hb
  have h9 (q : Pattern) (ha : d209458 q = 1) (hb : d210781 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209458, d210781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209458, d210781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209459 q = 1) (hb : d210782 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209459, d210782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209459, d210782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209460 q = 1) (hb : d210783 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209460, d210783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209460, d210783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209461 q = 1) (hb : d210784 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209461, d210784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209461, d210784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209462 q = 1) (hb : d210785 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209462, d210785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209462, d210785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro51084 (p : Pattern) (ha : d209468 p = 1) (hb : d210791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209463 q = 1) (hb : d210786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209463, d210786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51083 q ha hb
    | true =>
      simp only [d209463, d210786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209464 q = 1) (hb : d210787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209464, d210787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209464, d210787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209465 q = 1) (hb : d210788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209465, d210788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209465, d210788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209466 q = 1) (hb : d210789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209466, d210789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209466, d210789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209467 q = 1) (hb : d210790 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209467, d210790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209467, d210790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209468 q = 1) (hb : d210791 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209468, d210791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209468, d210791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51085 (p : Pattern) (ha : d209474 p = 1) (hb : d210797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209449 q = 1) (hb : d210777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209449, d210777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51078 q ha hb
    | true =>
      simp only [d209449, d210777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51080 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d210778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d210778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209455, d210778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209469 q = 1) (hb : d210792 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209469, d210792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51084 q ha hb
    | true =>
      simp only [d209469, d210792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209470 q = 1) (hb : d210793 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209470, d210793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209470, d210793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209471 q = 1) (hb : d210794 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d210794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d210794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209472 q = 1) (hb : d210795 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d210795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d210795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209473 q = 1) (hb : d210796 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d210796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d210796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209474 q = 1) (hb : d210797 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d210797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d210797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51086 (p : Pattern) (ha : d209453 p = 1) (hb : d210802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209443 q = 1) (hb : d210771 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209443, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51079 q ha hb
    | true =>
      simp only [d209443, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209444 q = 1) (hb : d210772 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209444, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209444, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209450 q = 1) (hb : d210799 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209450, d210799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209450, d210799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209451 q = 1) (hb : d210800 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209451, d210800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209451, d210800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209452 q = 1) (hb : d210801 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209452, d210801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209452, d210801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209453 q = 1) (hb : d210802 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209453, d210802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209453, d210802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51087 (p : Pattern) (ha : d209481 p = 1) (hb : d210808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209476 q = 1) (hb : d210803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209476, d210803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51086 q ha hb
    | true =>
      simp only [d209476, d210803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209477 q = 1) (hb : d210804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209477, d210804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209477, d210804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209478 q = 1) (hb : d210805 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209478, d210805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209478, d210805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209479 q = 1) (hb : d210806 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209479, d210806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209479, d210806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209480 q = 1) (hb : d210807 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209480, d210807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209480, d210807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209481 q = 1) (hb : d210808 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209481, d210808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209481, d210808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51088 (p : Pattern) (ha : d209487 p = 1) (hb : d210814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209284 q = 1) (hb : d210644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209284, d210644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209284, d210644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51044 q ha hb
  have h2 (q : Pattern) (ha : d209285 q = 1) (hb : d210645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209285, d210645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209285, d210645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209294 q = 1) (hb : d210654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209294, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51044 q ha hb
    | true =>
      simp only [d209294, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51047 q ha hb
  have h4 (q : Pattern) (ha : d209295 q = 1) (hb : d210655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209295, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209295, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209296 q = 1) (hb : d210656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209296, d210656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209296, d210656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209370 q = 1) (hb : d210724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d210724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51060 q ha hb
    | true =>
      simp only [d209370, d210724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51067 q ha hb
  have h7 (q : Pattern) (ha : d209383 q = 1) (hb : d210737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209383, d210737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51068 q ha hb
    | true =>
      simp only [d209383, d210737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51069 q ha hb
  have h8 (q : Pattern) (ha : d209384 q = 1) (hb : d210738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d210738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209384, d210738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209385 q = 1) (hb : d210739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d210739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209385, d210739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209386 q = 1) (hb : d210740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d210740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209386, d210740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209390 q = 1) (hb : d210744 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d210744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209390, d210744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51070 q ha hb
  have h12 (q : Pattern) (ha : d209392 q = 1) (hb : d210746 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209392, d210746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209392, d210746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51071 q ha hb
  have h13 (q : Pattern) (ha : d209393 q = 1) (hb : d210747 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d210747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209393, d210747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209394 q = 1) (hb : d210748 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d210748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209394, d210748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209395 q = 1) (hb : d210749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d210749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209395, d210749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209396 q = 1) (hb : d210750 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d210750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209396, d210750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209475 q = 1) (hb : d210798 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d210798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209475, d210798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51085 q ha hb
  have h18 (q : Pattern) (ha : d209482 q = 1) (hb : d210809 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209482, d210809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209482, d210809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51087 q ha hb
  have h19 (q : Pattern) (ha : d209483 q = 1) (hb : d210810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d210810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209483, d210810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209484 q = 1) (hb : d210811 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d210811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209484, d210811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209485 q = 1) (hb : d210812 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d210812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209485, d210812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209486 q = 1) (hb : d210813 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d210813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209486, d210813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209487 q = 1) (hb : d210814 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d210814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209487, d210814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro51089 (p : Pattern) (ha : d209493 p = 1) (hb : d210820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d210815 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d210815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d210815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51088 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d210816 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d210816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d210816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d210817 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d210817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d210817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d210818 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d210818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d210818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d210819 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d210819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d210819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d210820 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d210820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d210820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51090 (p : Pattern) (ha : d209499 p = 1) (hb : d210826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d209917 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d209917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50832 q ha hb
    | true =>
      simp only [d208438, d209917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50873 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d210127 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d210127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d210127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50921 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d210128 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d210128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d210128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d210369 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d210369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d210369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50978 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d210370 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d210370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d210370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d210371 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d210371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d210371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d210612 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d210612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d210612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51034 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d210613 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d210613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d210613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d210614 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d210614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d210614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d210615 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d210615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d210615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d210821 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d210821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d210821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51089 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d210822 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d210822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d210822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d210823 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d210823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d210823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d210824 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d210824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d210824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d210825 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d210825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d210825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d210826 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d210826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d210826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro51091 (p : Pattern) (ha : d209505 p = 1) (hb : d210832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d210827 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d210827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51090 q ha hb
    | true =>
      simp only [d209500, d210827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d210828 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d210828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d210828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d210829 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d210829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d210829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d210830 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d210830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d210830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d210831 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d210831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d210831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d210832 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d210832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d210832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51092 (p : Pattern) (ha : d209511 p = 1) (hb : d210838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d210833 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d210833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51091 q ha hb
    | true =>
      simp only [d209506, d210833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d210834 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d210834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d210834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d210835 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d210835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d210835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d210836 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d210836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d210836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d210837 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d210837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d210837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d210838 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d210838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d210838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51093 (p : Pattern) (ha : d209517 p = 1) (hb : d210844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d210839 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d210839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51092 q ha hb
    | true =>
      simp only [d209512, d210839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d210840 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d210840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d210840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d210841 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d210841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d210841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d210842 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d210842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d210842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d210843 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d210843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d210843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d210844 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d210844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d210844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51094 (p : Pattern) (ha : d209523 p = 1) (hb : d210850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d210845 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d210845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51093 q ha hb
    | true =>
      simp only [d209518, d210845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d210846 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d210846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d210846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d210847 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d210847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d210847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d210848 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d210848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d210848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d210849 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d210849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d210849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d210850 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d210850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d210850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51095 (p : Pattern) (ha : d209529 p = 1) (hb : d210856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d210851 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d210851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51094 q ha hb
    | true =>
      simp only [d209524, d210851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d210852 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d210852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d210852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d210853 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d210853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d210853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d210854 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d210854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d210854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d210855 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d210855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d210855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d210856 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d210856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d210856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51096 (p : Pattern) (ha : d209535 p = 1) (hb : d210862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d210857 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d210857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51095 q ha hb
    | true =>
      simp only [d209530, d210857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d210858 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d210858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d210858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d210859 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d210859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d210859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d210860 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d210860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d210860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d210861 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d210861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d210861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d210862 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d210862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d210862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51097 (p : Pattern) (ha : d209541 p = 1) (hb : d210868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d210863 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d210863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51096 q ha hb
    | true =>
      simp only [d209536, d210863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d210864 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d210864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d210864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d210865 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d210865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d210865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d210866 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d210866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d210866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d210867 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d210867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d210867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d210868 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d210868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d210868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51098 (p : Pattern) (ha : d194340 p = 1) (hb : d208035 p = 1) : d210871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50470 q ha hb
    | true =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d208035 q = 1) : d209615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20970 q = 1) (hb : d208035 q = 1) : d209616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20971 q = 1) (hb : d208035 q = 1) : d209617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20972 q = 1) (hb : d208035 q = 1) : d209618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194340 q = 1) (hb : d208035 q = 1) : d210871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194340, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51099 (p : Pattern) (ha : d194350 p = 1) (hb : d208035 p = 1) : d210881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208035 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d208035 q = 1) : d209591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50475 q ha hb
    | true =>
      simp only [d20945, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194346 q = 1) (hb : d208035 q = 1) : d210877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194346, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194347 q = 1) (hb : d208035 q = 1) : d210878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194347, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194348 q = 1) (hb : d208035 q = 1) : d210879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194348, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194349 q = 1) (hb : d208035 q = 1) : d210880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194349, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194350 q = 1) (hb : d208035 q = 1) : d210881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194350, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51100 (p : Pattern) (ha : d194356 p = 1) (hb : d208035 p = 1) : d210887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d208035 q = 1) : d209620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50478 q ha hb
    | true =>
      simp only [d20974, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50479 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d208035 q = 1) : d209621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194338 q = 1) (hb : d208035 q = 1) : d210869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194338, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194339 q = 1) (hb : d208035 q = 1) : d210870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194339, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194341 q = 1) (hb : d208035 q = 1) : d210872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194341, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51098 q ha hb
  have h6 (q : Pattern) (ha : d194342 q = 1) (hb : d208035 q = 1) : d210873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194343 q = 1) (hb : d208035 q = 1) : d210874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194344 q = 1) (hb : d208035 q = 1) : d210875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194345 q = 1) (hb : d208035 q = 1) : d210876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194351 q = 1) (hb : d208035 q = 1) : d210882 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194351, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51099 q ha hb
  have h11 (q : Pattern) (ha : d194352 q = 1) (hb : d208035 q = 1) : d210883 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194353 q = 1) (hb : d208035 q = 1) : d210884 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194354 q = 1) (hb : d208035 q = 1) : d210885 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194355 q = 1) (hb : d208035 q = 1) : d210886 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194356 q = 1) (hb : d208035 q = 1) : d210887 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51101 (p : Pattern) (ha : d194362 p = 1) (hb : d208035 p = 1) : d210893 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d208035 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d194357 q = 1) (hb : d208035 q = 1) : d210888 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194357, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51100 q ha hb
  have h3 (q : Pattern) (ha : d194358 q = 1) (hb : d208035 q = 1) : d210889 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194358, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194359 q = 1) (hb : d208035 q = 1) : d210890 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194359, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194360 q = 1) (hb : d208035 q = 1) : d210891 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194360, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194361 q = 1) (hb : d208035 q = 1) : d210892 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194361, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194362 q = 1) (hb : d208035 q = 1) : d210893 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194362, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51102 (p : Pattern) (ha : d194365 p = 1) (hb : d208035 p = 1) : d210896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d208035 q = 1) : d209757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50508 q ha hb
    | true =>
      simp only [d21156, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50509 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d208035 q = 1) : d209758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d208035 q = 1) : d209759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d208035 q = 1) : d209760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d208035 q = 1) : d209761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194365 q = 1) (hb : d208035 q = 1) : d210896 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194365, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51103 (p : Pattern) (ha : d194376 p = 1) (hb : d208035 p = 1) : d210907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194371 q = 1) (hb : d208035 q = 1) : d210902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d210902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50542 q ha hb
    | true =>
      simp only [d194371, d210902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50515 q ha hb
  have h2 (q : Pattern) (ha : d194372 q = 1) (hb : d208035 q = 1) : d210903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194372, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194373 q = 1) (hb : d208035 q = 1) : d210904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194374 q = 1) (hb : d208035 q = 1) : d210905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194374, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194375 q = 1) (hb : d208035 q = 1) : d210906 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194375, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194376 q = 1) (hb : d208035 q = 1) : d210907 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194376, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51104 (p : Pattern) (ha : d194382 p = 1) (hb : d208035 p = 1) : d210913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d208035 q = 1) : d209763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50507 q ha hb
    | true =>
      simp only [d21162, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50510 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d208035 q = 1) : d209764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194363 q = 1) (hb : d208035 q = 1) : d210894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194363, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194364 q = 1) (hb : d208035 q = 1) : d210895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194364, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194366 q = 1) (hb : d208035 q = 1) : d210897 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194366, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51102 q ha hb
  have h6 (q : Pattern) (ha : d194367 q = 1) (hb : d208035 q = 1) : d210898 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194368 q = 1) (hb : d208035 q = 1) : d210899 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194369 q = 1) (hb : d208035 q = 1) : d210900 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194370 q = 1) (hb : d208035 q = 1) : d210901 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194377 q = 1) (hb : d208035 q = 1) : d210908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194377, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51103 q ha hb
  have h11 (q : Pattern) (ha : d194378 q = 1) (hb : d208035 q = 1) : d210909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194379 q = 1) (hb : d208035 q = 1) : d210910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194380 q = 1) (hb : d208035 q = 1) : d210911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194381 q = 1) (hb : d208035 q = 1) : d210912 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194382 q = 1) (hb : d208035 q = 1) : d210913 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51105 (p : Pattern) (ha : d194388 p = 1) (hb : d208035 p = 1) : d210919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194383 q = 1) (hb : d208035 q = 1) : d210914 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194383, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51104 q ha hb
  have h2 (q : Pattern) (ha : d194384 q = 1) (hb : d208035 q = 1) : d210915 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194384, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194385 q = 1) (hb : d208035 q = 1) : d210916 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194385, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194386 q = 1) (hb : d208035 q = 1) : d210917 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194386, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194387 q = 1) (hb : d208035 q = 1) : d210918 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194387, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194388 q = 1) (hb : d208035 q = 1) : d210919 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194388, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51106 (p : Pattern) (ha : d194392 p = 1) (hb : d208035 p = 1) : d210923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d208035 q = 1) : d209955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50555 q ha hb
    | true =>
      simp only [d21455, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50556 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d208035 q = 1) : d209956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d208035 q = 1) : d209957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d208035 q = 1) : d209958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d208035 q = 1) : d209959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194392 q = 1) (hb : d208035 q = 1) : d210923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194392, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51107 (p : Pattern) (ha : d194403 p = 1) (hb : d208035 p = 1) : d210934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194398 q = 1) (hb : d208035 q = 1) : d210929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d210929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50592 q ha hb
    | true =>
      simp only [d194398, d210929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50564 q ha hb
  have h2 (q : Pattern) (ha : d194399 q = 1) (hb : d208035 q = 1) : d210930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194399, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194400 q = 1) (hb : d208035 q = 1) : d210931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194401 q = 1) (hb : d208035 q = 1) : d210932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194401, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194402 q = 1) (hb : d208035 q = 1) : d210933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194402, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194403 q = 1) (hb : d208035 q = 1) : d210934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194403, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51108 (p : Pattern) (ha : d194409 p = 1) (hb : d208035 p = 1) : d210940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d208035 q = 1) : d209961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50554 q ha hb
    | true =>
      simp only [d21461, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50557 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d208035 q = 1) : d209962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194390 q = 1) (hb : d208035 q = 1) : d210921 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194390, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194391 q = 1) (hb : d208035 q = 1) : d210922 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194391, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194393 q = 1) (hb : d208035 q = 1) : d210924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194393, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51106 q ha hb
  have h6 (q : Pattern) (ha : d194394 q = 1) (hb : d208035 q = 1) : d210925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194395 q = 1) (hb : d208035 q = 1) : d210926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194396 q = 1) (hb : d208035 q = 1) : d210927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194397 q = 1) (hb : d208035 q = 1) : d210928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194404 q = 1) (hb : d208035 q = 1) : d210935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194404, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51107 q ha hb
  have h11 (q : Pattern) (ha : d194405 q = 1) (hb : d208035 q = 1) : d210936 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194406 q = 1) (hb : d208035 q = 1) : d210937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194407 q = 1) (hb : d208035 q = 1) : d210938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194408 q = 1) (hb : d208035 q = 1) : d210939 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194409 q = 1) (hb : d208035 q = 1) : d210940 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51109 (p : Pattern) (ha : d194415 p = 1) (hb : d208035 p = 1) : d210946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194410 q = 1) (hb : d208035 q = 1) : d210941 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194410, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51108 q ha hb
  have h2 (q : Pattern) (ha : d194411 q = 1) (hb : d208035 q = 1) : d210942 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194411, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194412 q = 1) (hb : d208035 q = 1) : d210943 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194412, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194413 q = 1) (hb : d208035 q = 1) : d210944 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194413, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194414 q = 1) (hb : d208035 q = 1) : d210945 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194414, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194415 q = 1) (hb : d208035 q = 1) : d210946 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194415, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51110 (p : Pattern) (ha : d194420 p = 1) (hb : d208035 p = 1) : d210951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d208035 q = 1) : d210173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50613 q ha hb
    | true =>
      simp only [d21808, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50614 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d208035 q = 1) : d210174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d208035 q = 1) : d210175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d208035 q = 1) : d210176 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d208035 q = 1) : d210177 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194420 q = 1) (hb : d208035 q = 1) : d210951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194420, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51111 (p : Pattern) (ha : d194427 p = 1) (hb : d208035 p = 1) : d210310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d208035 q = 1) : d210295 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d210295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50650 q ha hb
    | true =>
      simp only [d22070, d210295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50621 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d208035 q = 1) : d210296 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d210296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d210296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d208035 q = 1) : d210297 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d210297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d210297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d208035 q = 1) : d210300 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50621 q ha hb
    | true =>
      simp only [d22079, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50652 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d208035 q = 1) : d210301 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d208035 q = 1) : d210302 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d208035 q = 1) : d210303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d210303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d210303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22098 q = 1) (hb : d208035 q = 1) : d210300 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50621 q ha hb
    | true =>
      simp only [d22098, d210300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50622 q ha hb
  have h9 (q : Pattern) (ha : d22099 q = 1) (hb : d208035 q = 1) : d210301 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d210301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22100 q = 1) (hb : d208035 q = 1) : d210302 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d210302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22101 q = 1) (hb : d208035 q = 1) : d210308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d210308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22101, d210308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194426 q = 1) (hb : d208035 q = 1) : d210309 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d210309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194426, d210309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194427 q = 1) (hb : d208035 q = 1) : d210310 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d210310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194427, d210310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51112 (p : Pattern) (ha : d194433 p = 1) (hb : d208035 p = 1) : d210324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194428 q = 1) (hb : d208035 q = 1) : d210311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d210311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51111 q ha hb
    | true =>
      simp only [d194428, d210311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194429 q = 1) (hb : d208035 q = 1) : d210312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d210312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194429, d210312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d208035 q = 1) : d210319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d210319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50623 q ha hb
    | true =>
      simp only [d22104, d210319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d208035 q = 1) : d210320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d210320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d210320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194430 q = 1) (hb : d208035 q = 1) : d210321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d210321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d210321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194431 q = 1) (hb : d208035 q = 1) : d210322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d210322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d210322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194432 q = 1) (hb : d208035 q = 1) : d210323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d210323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d210323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194433 q = 1) (hb : d208035 q = 1) : d210324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d210324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d210324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51113 (p : Pattern) (ha : d194439 p = 1) (hb : d208035 p = 1) : d210962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194434 q = 1) (hb : d208035 q = 1) : d210957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d210957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51112 q ha hb
    | true =>
      simp only [d194434, d210957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50624 q ha hb
  have h2 (q : Pattern) (ha : d194435 q = 1) (hb : d208035 q = 1) : d210958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194435, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194436 q = 1) (hb : d208035 q = 1) : d210959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194437 q = 1) (hb : d208035 q = 1) : d210960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194437, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194438 q = 1) (hb : d208035 q = 1) : d210961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194438, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194439 q = 1) (hb : d208035 q = 1) : d210962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194439, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51114 (p : Pattern) (ha : d194445 p = 1) (hb : d208035 p = 1) : d210968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d208035 q = 1) : d210179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50612 q ha hb
    | true =>
      simp only [d21814, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50615 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d208035 q = 1) : d210180 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194418 q = 1) (hb : d208035 q = 1) : d210949 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194418, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194419 q = 1) (hb : d208035 q = 1) : d210950 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194419, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194421 q = 1) (hb : d208035 q = 1) : d210952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194421, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51110 q ha hb
  have h6 (q : Pattern) (ha : d194422 q = 1) (hb : d208035 q = 1) : d210953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194423 q = 1) (hb : d208035 q = 1) : d210954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194424 q = 1) (hb : d208035 q = 1) : d210955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194425 q = 1) (hb : d208035 q = 1) : d210956 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194440 q = 1) (hb : d208035 q = 1) : d210963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194440, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51113 q ha hb
  have h11 (q : Pattern) (ha : d194441 q = 1) (hb : d208035 q = 1) : d210964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194442 q = 1) (hb : d208035 q = 1) : d210965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194443 q = 1) (hb : d208035 q = 1) : d210966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194444 q = 1) (hb : d208035 q = 1) : d210967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194445 q = 1) (hb : d208035 q = 1) : d210968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51115 (p : Pattern) (ha : d194451 p = 1) (hb : d208035 p = 1) : d210974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194446 q = 1) (hb : d208035 q = 1) : d210969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194446, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51114 q ha hb
  have h2 (q : Pattern) (ha : d194447 q = 1) (hb : d208035 q = 1) : d210970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194447, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194448 q = 1) (hb : d208035 q = 1) : d210971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194448, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194449 q = 1) (hb : d208035 q = 1) : d210972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194449, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194450 q = 1) (hb : d208035 q = 1) : d210973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194450, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194451 q = 1) (hb : d208035 q = 1) : d210974 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194451, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51116 (p : Pattern) (ha : d194457 p = 1) (hb : d208035 p = 1) : d210980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d208035 q = 1) : d210416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50678 q ha hb
    | true =>
      simp only [d22286, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50679 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d208035 q = 1) : d210417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d208035 q = 1) : d210418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d208035 q = 1) : d210419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d208035 q = 1) : d210420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194457 q = 1) (hb : d208035 q = 1) : d210980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194457, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51117 (p : Pattern) (ha : d194464 p = 1) (hb : d208035 p = 1) : d210553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d208035 q = 1) : d210538 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50715 q ha hb
    | true =>
      simp only [d22535, d210538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50686 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d208035 q = 1) : d210539 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d210539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d208035 q = 1) : d210540 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d210540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d208035 q = 1) : d210543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50686 q ha hb
    | true =>
      simp only [d22544, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50717 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d208035 q = 1) : d210544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d208035 q = 1) : d210545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d208035 q = 1) : d210546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d210546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22563 q = 1) (hb : d208035 q = 1) : d210543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50686 q ha hb
    | true =>
      simp only [d22563, d210543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50687 q ha hb
  have h9 (q : Pattern) (ha : d22564 q = 1) (hb : d208035 q = 1) : d210544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d210544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22565 q = 1) (hb : d208035 q = 1) : d210545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d210545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22566 q = 1) (hb : d208035 q = 1) : d210551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22566, d210551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194463 q = 1) (hb : d208035 q = 1) : d210552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d210552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194463, d210552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194464 q = 1) (hb : d208035 q = 1) : d210553 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d210553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194464, d210553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51118 (p : Pattern) (ha : d194470 p = 1) (hb : d208035 p = 1) : d210567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194465 q = 1) (hb : d208035 q = 1) : d210554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51117 q ha hb
    | true =>
      simp only [d194465, d210554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194466 q = 1) (hb : d208035 q = 1) : d210555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194466, d210555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d208035 q = 1) : d210562 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50688 q ha hb
    | true =>
      simp only [d22569, d210562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d208035 q = 1) : d210563 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d210563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194467 q = 1) (hb : d208035 q = 1) : d210564 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d210564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d210564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194468 q = 1) (hb : d208035 q = 1) : d210565 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d210565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d210565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194469 q = 1) (hb : d208035 q = 1) : d210566 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d210566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d210566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194470 q = 1) (hb : d208035 q = 1) : d210567 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d210567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d210567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51119 (p : Pattern) (ha : d194476 p = 1) (hb : d208035 p = 1) : d210991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194471 q = 1) (hb : d208035 q = 1) : d210986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51118 q ha hb
    | true =>
      simp only [d194471, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50689 q ha hb
  have h2 (q : Pattern) (ha : d194472 q = 1) (hb : d208035 q = 1) : d210987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194472, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194473 q = 1) (hb : d208035 q = 1) : d210988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194474 q = 1) (hb : d208035 q = 1) : d210989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194474, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194475 q = 1) (hb : d208035 q = 1) : d210990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194475, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194476 q = 1) (hb : d208035 q = 1) : d210991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194476, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51120 (p : Pattern) (ha : d194482 p = 1) (hb : d208035 p = 1) : d210997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d208035 q = 1) : d210422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50677 q ha hb
    | true =>
      simp only [d22292, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50680 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d208035 q = 1) : d210423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194455 q = 1) (hb : d208035 q = 1) : d210978 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194455, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194456 q = 1) (hb : d208035 q = 1) : d210979 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194456, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194458 q = 1) (hb : d208035 q = 1) : d210981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194458, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51116 q ha hb
  have h6 (q : Pattern) (ha : d194459 q = 1) (hb : d208035 q = 1) : d210982 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194460 q = 1) (hb : d208035 q = 1) : d210983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194461 q = 1) (hb : d208035 q = 1) : d210984 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194462 q = 1) (hb : d208035 q = 1) : d210985 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194477 q = 1) (hb : d208035 q = 1) : d210992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194477, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51119 q ha hb
  have h11 (q : Pattern) (ha : d194478 q = 1) (hb : d208035 q = 1) : d210993 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194479 q = 1) (hb : d208035 q = 1) : d210994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194480 q = 1) (hb : d208035 q = 1) : d210995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194481 q = 1) (hb : d208035 q = 1) : d210996 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194482 q = 1) (hb : d208035 q = 1) : d210997 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51121 (p : Pattern) (ha : d194488 p = 1) (hb : d208035 p = 1) : d211003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194483 q = 1) (hb : d208035 q = 1) : d210998 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194483, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51120 q ha hb
  have h2 (q : Pattern) (ha : d194484 q = 1) (hb : d208035 q = 1) : d210999 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194484, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194485 q = 1) (hb : d208035 q = 1) : d211000 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194485, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194486 q = 1) (hb : d208035 q = 1) : d211001 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194486, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194487 q = 1) (hb : d208035 q = 1) : d211002 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194487, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194488 q = 1) (hb : d208035 q = 1) : d211003 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194488, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51122 (p : Pattern) (ha : d194495 p = 1) (hb : d208035 p = 1) : d211010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d208035 q = 1) : d210648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50742 q ha hb
    | true =>
      simp only [d22741, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50743 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d208035 q = 1) : d210649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d208035 q = 1) : d210650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d208035 q = 1) : d210651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d208035 q = 1) : d210652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194495 q = 1) (hb : d208035 q = 1) : d211010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194495, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51123 (p : Pattern) (ha : d194502 p = 1) (hb : d208035 p = 1) : d210762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d208035 q = 1) : d201628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50776 q ha hb
    | true =>
      simp only [d22949, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50750 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d208035 q = 1) : d201629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d208035 q = 1) : d201630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d208035 q = 1) : d210752 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50750 q ha hb
    | true =>
      simp only [d22958, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50777 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d208035 q = 1) : d210753 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d208035 q = 1) : d210754 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d208035 q = 1) : d210755 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d210755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22977 q = 1) (hb : d208035 q = 1) : d210752 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50750 q ha hb
    | true =>
      simp only [d22977, d210752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50751 q ha hb
  have h9 (q : Pattern) (ha : d22978 q = 1) (hb : d208035 q = 1) : d210753 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d210753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22979 q = 1) (hb : d208035 q = 1) : d210754 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d210754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22980 q = 1) (hb : d208035 q = 1) : d210760 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22980, d210760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194501 q = 1) (hb : d208035 q = 1) : d210761 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d210761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194501, d210761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194502 q = 1) (hb : d208035 q = 1) : d210762 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d210762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194502, d210762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51124 (p : Pattern) (ha : d194508 p = 1) (hb : d208035 p = 1) : d210776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194503 q = 1) (hb : d208035 q = 1) : d210763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51123 q ha hb
    | true =>
      simp only [d194503, d210763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194504 q = 1) (hb : d208035 q = 1) : d210764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194504, d210764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d208035 q = 1) : d210771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50752 q ha hb
    | true =>
      simp only [d22983, d210771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d208035 q = 1) : d210772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d210772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194505 q = 1) (hb : d208035 q = 1) : d210773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d210773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d210773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194506 q = 1) (hb : d208035 q = 1) : d210774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d210774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d210774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194507 q = 1) (hb : d208035 q = 1) : d210775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d210775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d210775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194508 q = 1) (hb : d208035 q = 1) : d210776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d210776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d210776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51125 (p : Pattern) (ha : d194514 p = 1) (hb : d208035 p = 1) : d211021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194509 q = 1) (hb : d208035 q = 1) : d211016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51124 q ha hb
    | true =>
      simp only [d194509, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50753 q ha hb
  have h2 (q : Pattern) (ha : d194510 q = 1) (hb : d208035 q = 1) : d211017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194510, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194511 q = 1) (hb : d208035 q = 1) : d211018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194512 q = 1) (hb : d208035 q = 1) : d211019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194512, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194513 q = 1) (hb : d208035 q = 1) : d211020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194513, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194514 q = 1) (hb : d208035 q = 1) : d211021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194514, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51126 (p : Pattern) (ha : d194520 p = 1) (hb : d208035 p = 1) : d211027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d208035 q = 1) : d210654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50741 q ha hb
    | true =>
      simp only [d22747, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50744 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d208035 q = 1) : d210655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194493 q = 1) (hb : d208035 q = 1) : d211008 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194493, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194494 q = 1) (hb : d208035 q = 1) : d211009 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194494, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194496 q = 1) (hb : d208035 q = 1) : d211011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194496, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51122 q ha hb
  have h6 (q : Pattern) (ha : d194497 q = 1) (hb : d208035 q = 1) : d211012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194498 q = 1) (hb : d208035 q = 1) : d211013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194499 q = 1) (hb : d208035 q = 1) : d211014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194500 q = 1) (hb : d208035 q = 1) : d211015 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194515 q = 1) (hb : d208035 q = 1) : d211022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194515, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51125 q ha hb
  have h11 (q : Pattern) (ha : d194516 q = 1) (hb : d208035 q = 1) : d211023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194517 q = 1) (hb : d208035 q = 1) : d211024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194518 q = 1) (hb : d208035 q = 1) : d211025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194519 q = 1) (hb : d208035 q = 1) : d211026 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194520 q = 1) (hb : d208035 q = 1) : d211027 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51127 (p : Pattern) (ha : d194526 p = 1) (hb : d208035 p = 1) : d211033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194521 q = 1) (hb : d208035 q = 1) : d211028 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194521, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51126 q ha hb
  have h2 (q : Pattern) (ha : d194522 q = 1) (hb : d208035 q = 1) : d211029 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194522, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194523 q = 1) (hb : d208035 q = 1) : d211030 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194523, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194524 q = 1) (hb : d208035 q = 1) : d211031 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194524, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194525 q = 1) (hb : d208035 q = 1) : d211032 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194525, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194526 q = 1) (hb : d208035 q = 1) : d211033 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194526, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51128 (p : Pattern) (ha : d194532 p = 1) (hb : d208035 p = 1) : d211039 p = 1 := by
  have h0 (q : Pattern) (ha : d194389 q = 1) (hb : d208035 q = 1) : d210920 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51101 q ha hb
    | true =>
      simp only [d194389, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51105 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d194416 q = 1) (hb : d208035 q = 1) : d210947 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194416, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51109 q ha hb
  have h3 (q : Pattern) (ha : d194417 q = 1) (hb : d208035 q = 1) : d210948 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194452 q = 1) (hb : d208035 q = 1) : d210975 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194452, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51115 q ha hb
  have h5 (q : Pattern) (ha : d194453 q = 1) (hb : d208035 q = 1) : d210976 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194453, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194454 q = 1) (hb : d208035 q = 1) : d210977 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194489 q = 1) (hb : d208035 q = 1) : d211004 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194489, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51121 q ha hb
  have h8 (q : Pattern) (ha : d194490 q = 1) (hb : d208035 q = 1) : d211005 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194490, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d194491 q = 1) (hb : d208035 q = 1) : d211006 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194491, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194492 q = 1) (hb : d208035 q = 1) : d211007 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d194527 q = 1) (hb : d208035 q = 1) : d211034 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194527, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51127 q ha hb
  have h12 (q : Pattern) (ha : d194528 q = 1) (hb : d208035 q = 1) : d211035 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194528, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194529 q = 1) (hb : d208035 q = 1) : d211036 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194529, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d194530 q = 1) (hb : d208035 q = 1) : d211037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194530, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d194531 q = 1) (hb : d208035 q = 1) : d211038 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d194532 q = 1) (hb : d208035 q = 1) : d211039 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro51129 (p : Pattern) (ha : d194538 p = 1) (hb : d208035 p = 1) : d211045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194533 q = 1) (hb : d208035 q = 1) : d211040 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51128 q ha hb
    | true =>
      simp only [d194533, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194534 q = 1) (hb : d208035 q = 1) : d211041 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194535 q = 1) (hb : d208035 q = 1) : d211042 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194536 q = 1) (hb : d208035 q = 1) : d211043 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194537 q = 1) (hb : d208035 q = 1) : d211044 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194538 q = 1) (hb : d208035 q = 1) : d211045 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51130 (p : Pattern) (ha : d194544 p = 1) (hb : d208035 p = 1) : d211051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194539 q = 1) (hb : d208035 q = 1) : d211046 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51129 q ha hb
    | true =>
      simp only [d194539, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194540 q = 1) (hb : d208035 q = 1) : d211047 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194541 q = 1) (hb : d208035 q = 1) : d211048 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194542 q = 1) (hb : d208035 q = 1) : d211049 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194543 q = 1) (hb : d208035 q = 1) : d211050 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194544 q = 1) (hb : d208035 q = 1) : d211051 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51131 (p : Pattern) (ha : d194550 p = 1) (hb : d208035 p = 1) : d211057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194545 q = 1) (hb : d208035 q = 1) : d211052 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51130 q ha hb
    | true =>
      simp only [d194545, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194546 q = 1) (hb : d208035 q = 1) : d211053 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194547 q = 1) (hb : d208035 q = 1) : d211054 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194548 q = 1) (hb : d208035 q = 1) : d211055 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194549 q = 1) (hb : d208035 q = 1) : d211056 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194550 q = 1) (hb : d208035 q = 1) : d211057 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194550, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51132 (p : Pattern) (ha : d194556 p = 1) (hb : d208035 p = 1) : d211063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194551 q = 1) (hb : d208035 q = 1) : d211058 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51131 q ha hb
    | true =>
      simp only [d194551, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194552 q = 1) (hb : d208035 q = 1) : d211059 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194553 q = 1) (hb : d208035 q = 1) : d211060 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194554 q = 1) (hb : d208035 q = 1) : d211061 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194555 q = 1) (hb : d208035 q = 1) : d211062 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194556 q = 1) (hb : d208035 q = 1) : d211063 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51133 (p : Pattern) (ha : d194562 p = 1) (hb : d208035 p = 1) : d211069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194557 q = 1) (hb : d208035 q = 1) : d211064 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51132 q ha hb
    | true =>
      simp only [d194557, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194558 q = 1) (hb : d208035 q = 1) : d211065 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194559 q = 1) (hb : d208035 q = 1) : d211066 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194560 q = 1) (hb : d208035 q = 1) : d211067 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194561 q = 1) (hb : d208035 q = 1) : d211068 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194562 q = 1) (hb : d208035 q = 1) : d211069 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51134 (p : Pattern) (ha : d194568 p = 1) (hb : d208035 p = 1) : d211075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194563 q = 1) (hb : d208035 q = 1) : d211070 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51133 q ha hb
    | true =>
      simp only [d194563, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194564 q = 1) (hb : d208035 q = 1) : d211071 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194565 q = 1) (hb : d208035 q = 1) : d211072 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194566 q = 1) (hb : d208035 q = 1) : d211073 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194567 q = 1) (hb : d208035 q = 1) : d211074 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194568 q = 1) (hb : d208035 q = 1) : d211075 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51135 (p : Pattern) (ha : d194574 p = 1) (hb : d208035 p = 1) : d211081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194569 q = 1) (hb : d208035 q = 1) : d211076 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51134 q ha hb
    | true =>
      simp only [d194569, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194570 q = 1) (hb : d208035 q = 1) : d211077 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194571 q = 1) (hb : d208035 q = 1) : d211078 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194572 q = 1) (hb : d208035 q = 1) : d211079 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194573 q = 1) (hb : d208035 q = 1) : d211080 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194574 q = 1) (hb : d208035 q = 1) : d211081 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51136 (p : Pattern) (ha : d104 p = 1) (hb : d208053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208048 q = 1) : d0 q = 1 := by
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
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d208049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d208049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d208049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d208050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d208050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d208050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d208051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d208051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d208051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d208052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d208052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d208052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d208053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d208053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d208053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51137 (p : Pattern) (ha : d111 p = 1) (hb : d208060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208048 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d208049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d208049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d208049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d208050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d208050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d208050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d208051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d208051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d208051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d208052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d208052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d208052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d208055 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d208056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d208056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d208056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d208057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d208057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d208057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d208058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d208058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d208058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d208059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d208059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d208059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d208060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d208060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d208060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51138 (p : Pattern) (ha : d406 p = 1) (hb : d208067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d208056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d208056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d208056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d208057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d208057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d208057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d208065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d208065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d208065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d208066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d208066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d208066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d208067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d208067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d208067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51139 (p : Pattern) (ha : d462 p = 1) (hb : d208090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208085 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d208086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d208086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d208086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d208087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d208087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d208087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d208088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d208088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d208088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d208089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d208089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d208089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d208090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d208090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d208090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51140 (p : Pattern) (ha : d53647 p = 1) (hb : d208096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d208061 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d208061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51136 q ha hb
    | true =>
      simp only [d112, d208061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51137 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d208062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d208062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d208062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d208063 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d208063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d208063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d208064 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d208064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d208064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d208068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d208068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d208068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51138 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d208069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d208069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d208069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d208070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d208070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d208070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d208071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d208071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d208071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d208072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d208072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d208072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d208091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d208091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d208091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51139 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d208092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d208092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d208092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d208093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d208093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d208093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d208094 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d208094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d208094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d208095 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d208095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d208095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d208096 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d208096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d208096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro51141 (p : Pattern) (ha : d208161 p = 1) (hb : d209612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208048 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208048, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50799 q ha hb
    | true =>
      simp only [d208048, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d208151 q = 1) (hb : d209608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208151, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208151, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208158 q = 1) (hb : d209609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208158, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208158, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208159 q = 1) (hb : d209610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208159, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208159, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208160 q = 1) (hb : d209611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208160, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208160, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208161 q = 1) (hb : d209612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208161, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208161, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51142 (p : Pattern) (ha : d208180 p = 1) (hb : d209619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208048 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208048, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50799 q ha hb
    | true =>
      simp only [d208048, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d208151 q = 1) (hb : d209608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208151, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208151, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208158 q = 1) (hb : d209609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208158, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208158, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208159 q = 1) (hb : d209610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208159, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208159, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208160 q = 1) (hb : d209611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208160, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208160, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208166 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208170 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208055 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208055, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50801 q ha hb
    | true =>
      simp only [d208055, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d208173 q = 1) (hb : d209615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208173, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208173, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208177 q = 1) (hb : d209616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208177, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208177, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208178 q = 1) (hb : d209617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208178, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208178, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208179 q = 1) (hb : d209618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208179, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208179, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208180 q = 1) (hb : d209619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208180, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208180, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51143 (p : Pattern) (ha : d208189 p = 1) (hb : d210871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208055 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208055, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50801 q ha hb
    | true =>
      simp only [d208055, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d208173 q = 1) (hb : d209615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208173, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208173, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208177 q = 1) (hb : d209616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208177, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208177, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208187 q = 1) (hb : d209617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208187, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208187, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208188 q = 1) (hb : d209618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208188, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208188, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208189 q = 1) (hb : d210871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208189, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208189, d210871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51144 (p : Pattern) (ha : d208224 p = 1) (hb : d210881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208085 q = 1) (hb : d209591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208085, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50806 q ha hb
    | true =>
      simp only [d208085, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d208214 q = 1) (hb : d210877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208214, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208214, d210877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208220 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208221 q = 1) (hb : d210878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208221, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208221, d210878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208222 q = 1) (hb : d210879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208222, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208222, d210879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208223 q = 1) (hb : d210880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208223, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208223, d210880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208224 q = 1) (hb : d210881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208224, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208224, d210881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51145 (p : Pattern) (ha : d208230 p = 1) (hb : d210887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208116 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208181 q = 1) (hb : d209620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208181, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51141 q ha hb
    | true =>
      simp only [d208181, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51142 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208184 q = 1) (hb : d209621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208184, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208184, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208185 q = 1) (hb : d210869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208185, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208185, d210869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208186 q = 1) (hb : d210870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208186, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208186, d210870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208190 q = 1) (hb : d210872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208190, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208190, d210872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51143 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208191 q = 1) (hb : d210873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208191, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208191, d210873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208192 q = 1) (hb : d210874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208192, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208192, d210874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208193 q = 1) (hb : d210875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208193, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208193, d210875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208194 q = 1) (hb : d210876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208194, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208194, d210876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208225 q = 1) (hb : d210882 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208225, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208225, d210882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51144 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208226 q = 1) (hb : d210883 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208226, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208226, d210883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208227 q = 1) (hb : d210884 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208227, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208227, d210884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208228 q = 1) (hb : d210885 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208228, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208228, d210885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208229 q = 1) (hb : d210886 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208229, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208229, d210886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208230 q = 1) (hb : d210887 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208230, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208230, d210887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51146 (p : Pattern) (ha : d208236 p = 1) (hb : d210893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d208097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51140 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d208098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d208099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d208100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d208101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208231 q = 1) (hb : d210888 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208231, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208231, d210888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51145 q ha hb
  have h8 (q : Pattern) (ha : d208232 q = 1) (hb : d210889 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208232, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208232, d210889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208233 q = 1) (hb : d210890 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208233, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208233, d210890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208234 q = 1) (hb : d210891 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208234, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208234, d210891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208235 q = 1) (hb : d210892 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208235, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208235, d210892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208236 q = 1) (hb : d210893 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208236, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d208236, d210893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro51147 (p : Pattern) (ha : d208322 p = 1) (hb : d209752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208254 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208254, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50835 q ha hb
    | true =>
      simp only [d208254, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50836 q ha hb
  have h5 (q : Pattern) (ha : d208312 q = 1) (hb : d209748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208312, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208312, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208319 q = 1) (hb : d209749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208319, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208319, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208320 q = 1) (hb : d209750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208320, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208320, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208321 q = 1) (hb : d209751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208321, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208321, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208322 q = 1) (hb : d209752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208322, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208322, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51148 (p : Pattern) (ha : d208343 p = 1) (hb : d209762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208254 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208254, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50835 q ha hb
    | true =>
      simp only [d208254, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50836 q ha hb
  have h4 (q : Pattern) (ha : d208312 q = 1) (hb : d209748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208312, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208312, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208319 q = 1) (hb : d209749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208319, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208319, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208320 q = 1) (hb : d209750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208320, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208320, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208321 q = 1) (hb : d209751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208321, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208321, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208328 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208333 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208264 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208264, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50838 q ha hb
    | true =>
      simp only [d208264, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50839 q ha hb
  have h13 (q : Pattern) (ha : d208336 q = 1) (hb : d209758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208336, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208336, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208340 q = 1) (hb : d209759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208340, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208340, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208341 q = 1) (hb : d209760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208341, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208341, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208342 q = 1) (hb : d209761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208342, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208342, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208343 q = 1) (hb : d209762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208343, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208343, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51149 (p : Pattern) (ha : d208363 p = 1) (hb : d210896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208264 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208264, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50838 q ha hb
    | true =>
      simp only [d208264, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50839 q ha hb
  have h3 (q : Pattern) (ha : d208336 q = 1) (hb : d209758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208336, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208336, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208340 q = 1) (hb : d209759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208340, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208340, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208361 q = 1) (hb : d209760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208361, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208361, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208362 q = 1) (hb : d209761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208362, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208362, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208363 q = 1) (hb : d210896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208363, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208363, d210896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51150 (p : Pattern) (ha : d208418 p = 1) (hb : d210907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208407 q = 1) (hb : d210902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208407, d210902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50867 q ha hb
    | true =>
      simp only [d208407, d210902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50870 q ha hb
  have h3 (q : Pattern) (ha : d208408 q = 1) (hb : d210903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208408, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208408, d210903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208414 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208415 q = 1) (hb : d210904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208415, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208415, d210904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208416 q = 1) (hb : d210905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208416, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208416, d210905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208417 q = 1) (hb : d210906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208417, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208417, d210906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208418 q = 1) (hb : d210907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208418, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208418, d210907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51151 (p : Pattern) (ha : d208431 p = 1) (hb : d210913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208344 q = 1) (hb : d209763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208344, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51147 q ha hb
    | true =>
      simp only [d208344, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51148 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208358 q = 1) (hb : d209764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208358, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208358, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208359 q = 1) (hb : d210894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208359, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208359, d210894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208360 q = 1) (hb : d210895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208360, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208360, d210895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208364 q = 1) (hb : d210897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208364, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208364, d210897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51149 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208366 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208367 q = 1) (hb : d210898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208367, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208367, d210898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208368 q = 1) (hb : d210899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208368, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208368, d210899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208369 q = 1) (hb : d210900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208369, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208369, d210900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208370 q = 1) (hb : d210901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208370, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208370, d210901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208419 q = 1) (hb : d210908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208419, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208419, d210908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51150 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208426 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208427 q = 1) (hb : d210909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208427, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208427, d210909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208428 q = 1) (hb : d210910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208428, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208428, d210910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208429 q = 1) (hb : d210911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208429, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208429, d210911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208430 q = 1) (hb : d210912 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208430, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208430, d210912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208431 q = 1) (hb : d210913 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208431, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208431, d210913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51152 (p : Pattern) (ha : d208437 p = 1) (hb : d210919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208432 q = 1) (hb : d210914 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208432, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208432, d210914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51151 q ha hb
  have h2 (q : Pattern) (ha : d208433 q = 1) (hb : d210915 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208433, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208433, d210915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208434 q = 1) (hb : d210916 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208434, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208434, d210916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208435 q = 1) (hb : d210917 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208435, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208435, d210917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208436 q = 1) (hb : d210918 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208436, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208436, d210918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208437 q = 1) (hb : d210919 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208437, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208437, d210919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51153 (p : Pattern) (ha : d208534 p = 1) (hb : d209950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208466 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208466, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50880 q ha hb
    | true =>
      simp only [d208466, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50881 q ha hb
  have h5 (q : Pattern) (ha : d208524 q = 1) (hb : d209946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208524, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208524, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208531 q = 1) (hb : d209947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208531, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208531, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208532 q = 1) (hb : d209948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208532, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208532, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208533 q = 1) (hb : d209949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208533, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208533, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208534 q = 1) (hb : d209950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208534, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208534, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51154 (p : Pattern) (ha : d208555 p = 1) (hb : d209960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208466 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208466, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50880 q ha hb
    | true =>
      simp only [d208466, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50881 q ha hb
  have h4 (q : Pattern) (ha : d208524 q = 1) (hb : d209946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208524, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208524, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208531 q = 1) (hb : d209947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208531, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208531, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208532 q = 1) (hb : d209948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208532, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208532, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208533 q = 1) (hb : d209949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208533, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208533, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208545 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208476 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208476, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50883 q ha hb
    | true =>
      simp only [d208476, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50884 q ha hb
  have h13 (q : Pattern) (ha : d208548 q = 1) (hb : d209956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208548, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208548, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208552 q = 1) (hb : d209957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208552, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208552, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208553 q = 1) (hb : d209958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208553, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208553, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208554 q = 1) (hb : d209959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208554, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208554, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208555 q = 1) (hb : d209960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208555, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208555, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51155 (p : Pattern) (ha : d208575 p = 1) (hb : d210923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208476 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208476, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50883 q ha hb
    | true =>
      simp only [d208476, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50884 q ha hb
  have h3 (q : Pattern) (ha : d208548 q = 1) (hb : d209956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208548, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208548, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208552 q = 1) (hb : d209957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208552, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208552, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208573 q = 1) (hb : d209958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208573, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208573, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208574 q = 1) (hb : d209959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208574, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208574, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208575 q = 1) (hb : d210923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208575, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208575, d210923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51156 (p : Pattern) (ha : d208640 p = 1) (hb : d210934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208629 q = 1) (hb : d210929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208629, d210929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50915 q ha hb
    | true =>
      simp only [d208629, d210929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50918 q ha hb
  have h3 (q : Pattern) (ha : d208630 q = 1) (hb : d210930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208630, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208630, d210930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208636 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208637 q = 1) (hb : d210931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208637, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208637, d210931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208638 q = 1) (hb : d210932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208638, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208638, d210932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208639 q = 1) (hb : d210933 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208639, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208639, d210933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208640 q = 1) (hb : d210934 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208640, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208640, d210934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51157 (p : Pattern) (ha : d208653 p = 1) (hb : d210940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208556 q = 1) (hb : d209961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208556, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51153 q ha hb
    | true =>
      simp only [d208556, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51154 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208569 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208570 q = 1) (hb : d209962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208570, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208570, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208571 q = 1) (hb : d210921 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208571, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208571, d210921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208572 q = 1) (hb : d210922 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208572, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208572, d210922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208576 q = 1) (hb : d210924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208576, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208576, d210924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51155 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208578 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208579 q = 1) (hb : d210925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208579, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208579, d210925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208580 q = 1) (hb : d210926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208580, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208580, d210926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208581 q = 1) (hb : d210927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208581, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208581, d210927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208582 q = 1) (hb : d210928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208582, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208582, d210928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208641 q = 1) (hb : d210935 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208641, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208641, d210935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51156 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208648 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208649 q = 1) (hb : d210936 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208649, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208649, d210936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208650 q = 1) (hb : d210937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208650, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208650, d210937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208651 q = 1) (hb : d210938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208651, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208651, d210938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208652 q = 1) (hb : d210939 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208652, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208652, d210939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208653 q = 1) (hb : d210940 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208653, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208653, d210940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51158 (p : Pattern) (ha : d208659 p = 1) (hb : d210946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208654 q = 1) (hb : d210941 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208654, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208654, d210941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51157 q ha hb
  have h2 (q : Pattern) (ha : d208655 q = 1) (hb : d210942 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208655, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208655, d210942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208656 q = 1) (hb : d210943 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208656, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208656, d210943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208657 q = 1) (hb : d210944 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208657, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208657, d210944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208658 q = 1) (hb : d210945 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208658, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208658, d210945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208659 q = 1) (hb : d210946 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208659, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208659, d210946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51159 (p : Pattern) (ha : d208790 p = 1) (hb : d210168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208713 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208713, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50930 q ha hb
    | true =>
      simp only [d208713, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50931 q ha hb
  have h5 (q : Pattern) (ha : d208771 q = 1) (hb : d210164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208771, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208771, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208787 q = 1) (hb : d210165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208787, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208787, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208788 q = 1) (hb : d210166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208788, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208788, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208789 q = 1) (hb : d210167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208789, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208789, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208790 q = 1) (hb : d210168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208790, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208790, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51160 (p : Pattern) (ha : d208811 p = 1) (hb : d210178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208713 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208713, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50930 q ha hb
    | true =>
      simp only [d208713, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50931 q ha hb
  have h4 (q : Pattern) (ha : d208771 q = 1) (hb : d210164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208771, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208771, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208787 q = 1) (hb : d210165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208787, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208787, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208788 q = 1) (hb : d210166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208788, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208788, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208789 q = 1) (hb : d210167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208789, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208789, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208796 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208723 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208723, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50933 q ha hb
    | true =>
      simp only [d208723, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50934 q ha hb
  have h13 (q : Pattern) (ha : d208804 q = 1) (hb : d210174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208804, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208804, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208808 q = 1) (hb : d210175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208808, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208808, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208809 q = 1) (hb : d210176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208809, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208809, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208810 q = 1) (hb : d210177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208810, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208810, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208811 q = 1) (hb : d210178 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208811, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208811, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51161 (p : Pattern) (ha : d208831 p = 1) (hb : d210951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208723 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208723, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50933 q ha hb
    | true =>
      simp only [d208723, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50934 q ha hb
  have h3 (q : Pattern) (ha : d208804 q = 1) (hb : d210174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208804, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208804, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208808 q = 1) (hb : d210175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208808, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208808, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208829 q = 1) (hb : d210176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208829, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208829, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208830 q = 1) (hb : d210177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208830, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208830, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208831 q = 1) (hb : d210951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208831, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208831, d210951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51162 (p : Pattern) (ha : d208920 p = 1) (hb : d210962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208895 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208900 q = 1) (hb : d210957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208900, d210957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50969 q ha hb
    | true =>
      simp only [d208900, d210957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50975 q ha hb
  have h3 (q : Pattern) (ha : d208901 q = 1) (hb : d210958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208901, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208901, d210958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208917 q = 1) (hb : d210959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208917, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208917, d210959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208918 q = 1) (hb : d210960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208918, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208918, d210960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208919 q = 1) (hb : d210961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208919, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208919, d210961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208920 q = 1) (hb : d210962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208920, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208920, d210962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51163 (p : Pattern) (ha : d208933 p = 1) (hb : d210968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208812 q = 1) (hb : d210179 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208812, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51159 q ha hb
    | true =>
      simp only [d208812, d210179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51160 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208825 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208826 q = 1) (hb : d210180 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208826, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208826, d210180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208827 q = 1) (hb : d210949 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208827, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208827, d210949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208828 q = 1) (hb : d210950 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208828, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208828, d210950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208832 q = 1) (hb : d210952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208832, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208832, d210952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51161 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208834 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208835 q = 1) (hb : d210953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208835, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208835, d210953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208836 q = 1) (hb : d210954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208836, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208836, d210954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208837 q = 1) (hb : d210955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208837, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208837, d210955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208838 q = 1) (hb : d210956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208838, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208838, d210956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208921 q = 1) (hb : d210963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208921, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208921, d210963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51162 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208928 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208929 q = 1) (hb : d210964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208929, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208929, d210964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208930 q = 1) (hb : d210965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208930, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208930, d210965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208931 q = 1) (hb : d210966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208931, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208931, d210966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208932 q = 1) (hb : d210967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208932, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208932, d210967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208933 q = 1) (hb : d210968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208933, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208933, d210968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51164 (p : Pattern) (ha : d208939 p = 1) (hb : d210974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208934 q = 1) (hb : d210969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208934, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208934, d210969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51163 q ha hb
  have h2 (q : Pattern) (ha : d208935 q = 1) (hb : d210970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208935, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208935, d210970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208936 q = 1) (hb : d210971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208936, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208936, d210971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208937 q = 1) (hb : d210972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208937, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208937, d210972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208938 q = 1) (hb : d210973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208938, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208938, d210973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208939 q = 1) (hb : d210974 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208939, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208939, d210974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51165 (p : Pattern) (ha : d209073 p = 1) (hb : d210411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208996 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50987 q ha hb
    | true =>
      simp only [d208996, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50988 q ha hb
  have h5 (q : Pattern) (ha : d209054 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209054, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209070 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209070, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d209071 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209071, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209072 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209072, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209073 q = 1) (hb : d210411 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209073, d210411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209073, d210411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51166 (p : Pattern) (ha : d209094 p = 1) (hb : d210421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208996 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50987 q ha hb
    | true =>
      simp only [d208996, d210406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50988 q ha hb
  have h4 (q : Pattern) (ha : d209054 q = 1) (hb : d210407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209054, d210407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209070 q = 1) (hb : d210408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209070, d210408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209071 q = 1) (hb : d210409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209071, d210409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209072 q = 1) (hb : d210410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209072, d210410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209079 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209084 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d209006 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50990 q ha hb
    | true =>
      simp only [d209006, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50991 q ha hb
  have h13 (q : Pattern) (ha : d209087 q = 1) (hb : d210417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d209087, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209091 q = 1) (hb : d210418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209091, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209092 q = 1) (hb : d210419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209092, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209092, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209093 q = 1) (hb : d210420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209093, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209093, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209094 q = 1) (hb : d210421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209094, d210421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209094, d210421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51167 (p : Pattern) (ha : d209114 p = 1) (hb : d210980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209006 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50990 q ha hb
    | true =>
      simp only [d209006, d210416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50991 q ha hb
  have h3 (q : Pattern) (ha : d209087 q = 1) (hb : d210417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209087, d210417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209091 q = 1) (hb : d210418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209091, d210418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209112 q = 1) (hb : d210419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209112, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209112, d210419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209113 q = 1) (hb : d210420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209113, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209113, d210420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209114 q = 1) (hb : d210980 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d210980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51168 (p : Pattern) (ha : d209203 p = 1) (hb : d210991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209178 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209183 q = 1) (hb : d210986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209183, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51025 q ha hb
    | true =>
      simp only [d209183, d210986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51031 q ha hb
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d210987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209184, d210987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209199 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209200 q = 1) (hb : d210988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d210988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209201 q = 1) (hb : d210989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d210989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209202 q = 1) (hb : d210990 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d210990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209203 q = 1) (hb : d210991 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d210991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51169 (p : Pattern) (ha : d209216 p = 1) (hb : d210997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209095 q = 1) (hb : d210422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209095, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51165 q ha hb
    | true =>
      simp only [d209095, d210422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51166 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209109 q = 1) (hb : d210423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209109, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209109, d210423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209110 q = 1) (hb : d210978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209110, d210978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209111 q = 1) (hb : d210979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209111, d210979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209115 q = 1) (hb : d210981 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209115, d210981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51167 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209117 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209118 q = 1) (hb : d210982 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209118, d210982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209119 q = 1) (hb : d210983 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209119, d210983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209120 q = 1) (hb : d210984 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209120, d210984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209121 q = 1) (hb : d210985 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209121, d210985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209204 q = 1) (hb : d210992 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209204, d210992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51168 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209212 q = 1) (hb : d210993 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209212, d210993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209213 q = 1) (hb : d210994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209213, d210994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209214 q = 1) (hb : d210995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209214, d210995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209215 q = 1) (hb : d210996 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209215, d210996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209216 q = 1) (hb : d210997 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209216, d210997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51170 (p : Pattern) (ha : d209222 p = 1) (hb : d211003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d210998 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d210998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51169 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d210999 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d210999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d211000 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d211000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d211001 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d211001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d211002 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d211002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d211003 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d211003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51171 (p : Pattern) (ha : d209348 p = 1) (hb : d210643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d209278 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
    | true =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
  have h5 (q : Pattern) (ha : d209329 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209329, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209345 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209345, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d209346 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209346, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209347 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209347, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209348 q = 1) (hb : d210643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d210643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51172 (p : Pattern) (ha : d209369 p = 1) (hb : d210653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209278 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51042 q ha hb
    | true =>
      simp only [d209278, d210638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51043 q ha hb
  have h4 (q : Pattern) (ha : d209329 q = 1) (hb : d210639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209329, d210639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209345 q = 1) (hb : d210640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209345, d210640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209346 q = 1) (hb : d210641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209346, d210641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209347 q = 1) (hb : d210642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209347, d210642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209354 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d209288 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51045 q ha hb
    | true =>
      simp only [d209288, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51046 q ha hb
  have h13 (q : Pattern) (ha : d209362 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d209362, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209366 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209366, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209367 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209367, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209368 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209368, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209369 q = 1) (hb : d210653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209369, d210653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51173 (p : Pattern) (ha : d209389 p = 1) (hb : d211010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209288 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51045 q ha hb
    | true =>
      simp only [d209288, d210648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51046 q ha hb
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d210649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209362, d210649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209366 q = 1) (hb : d210650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d210650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209387 q = 1) (hb : d210651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d210651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209388 q = 1) (hb : d210652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d210652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209389 q = 1) (hb : d211010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d211010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51174 (p : Pattern) (ha : d209474 p = 1) (hb : d211021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209454 q = 1) (hb : d211016 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209454, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51080 q ha hb
    | true =>
      simp only [d209454, d211016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51086 q ha hb
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d211017 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209455, d211017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209470 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209471 q = 1) (hb : d211018 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d211018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209472 q = 1) (hb : d211019 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d211019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209473 q = 1) (hb : d211020 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d211020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209474 q = 1) (hb : d211021 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d211021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51175 (p : Pattern) (ha : d209487 p = 1) (hb : d211027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209296 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209370 q = 1) (hb : d210654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51171 q ha hb
    | true =>
      simp only [d209370, d210654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51172 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209384 q = 1) (hb : d210655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209384, d210655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209385 q = 1) (hb : d211008 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209385, d211008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209386 q = 1) (hb : d211009 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209386, d211009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209390 q = 1) (hb : d211011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209390, d211011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51173 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209392 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209393 q = 1) (hb : d211012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209393, d211012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209394 q = 1) (hb : d211013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209394, d211013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209395 q = 1) (hb : d211014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209395, d211014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209396 q = 1) (hb : d211015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209396, d211015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209475 q = 1) (hb : d211022 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209475, d211022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51174 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209482 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209483 q = 1) (hb : d211023 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209483, d211023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209484 q = 1) (hb : d211024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209484, d211024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209485 q = 1) (hb : d211025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209485, d211025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209486 q = 1) (hb : d211026 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209486, d211026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209487 q = 1) (hb : d211027 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209487, d211027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51176 (p : Pattern) (ha : d209493 p = 1) (hb : d211033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d211028 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d211028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51175 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d211029 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d211029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d211030 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d211030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d211031 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d211031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d211032 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d211032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d211033 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d211033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51177 (p : Pattern) (ha : d209499 p = 1) (hb : d211039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d210920 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51146 q ha hb
    | true =>
      simp only [d208438, d210920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51152 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d210947 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d210947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51158 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d210948 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d210948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d210975 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d210975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51164 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d210976 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d210976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d210977 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d210977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d211004 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d211004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51170 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d211005 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d211005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d211006 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d211006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d211007 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d211007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d211034 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d211034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51176 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d211035 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d211035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d211036 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d211036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d211037 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d211037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d211038 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d211038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d211039 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d211039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro51178 (p : Pattern) (ha : d209505 p = 1) (hb : d211045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d211040 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51177 q ha hb
    | true =>
      simp only [d209500, d211040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d211041 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d211041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d211042 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d211042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d211043 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d211043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d211044 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d211044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d211045 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d211045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51179 (p : Pattern) (ha : d209511 p = 1) (hb : d211051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d211046 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51178 q ha hb
    | true =>
      simp only [d209506, d211046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d211047 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d211047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d211048 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d211048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d211049 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d211049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d211050 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d211050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d211051 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d211051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51180 (p : Pattern) (ha : d209517 p = 1) (hb : d211057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d211052 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51179 q ha hb
    | true =>
      simp only [d209512, d211052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d211053 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d211053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d211054 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d211054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d211055 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d211055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d211056 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d211056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d211057 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d211057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51181 (p : Pattern) (ha : d209523 p = 1) (hb : d211063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d211058 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51180 q ha hb
    | true =>
      simp only [d209518, d211058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d211059 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d211059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d211060 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d211060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d211061 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d211061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d211062 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d211062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d211063 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d211063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51182 (p : Pattern) (ha : d209529 p = 1) (hb : d211069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d211064 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51181 q ha hb
    | true =>
      simp only [d209524, d211064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d211065 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d211065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d211066 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d211066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d211067 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d211067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d211068 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d211068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d211069 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d211069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51183 (p : Pattern) (ha : d209535 p = 1) (hb : d211075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d211070 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51182 q ha hb
    | true =>
      simp only [d209530, d211070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d211071 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d211071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d211072 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d211072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d211073 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d211073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d211074 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d211074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d211075 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d211075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51184 (p : Pattern) (ha : d209541 p = 1) (hb : d211081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d211076 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51183 q ha hb
    | true =>
      simp only [d209536, d211076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d211077 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d211077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d211078 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d211078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d211079 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d211079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d211080 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d211080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d211081 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d211081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51185 (p : Pattern) (ha : d104 p = 1) (hb : d211086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d211082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d211083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d211084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d211085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d211086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d211086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d211086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51186 (p : Pattern) (ha : d111 p = 1) (hb : d211091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d211082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d211083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d211084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d211085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d211087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d211088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d211089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d211089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d211089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d211090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d211090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d211090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d211091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d211091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d211091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51187 (p : Pattern) (ha : d406 p = 1) (hb : d211098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d211087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d211088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d211096 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d211096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d211096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d211097 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d211097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d211097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d211098 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d211098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d211098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51188 (p : Pattern) (ha : d462 p = 1) (hb : d211108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d211104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d211104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d211104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d211105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d211105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d211105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d211106 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d211106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d211106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d211107 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d211107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d211107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d211108 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d211108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d211108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51189 (p : Pattern) (ha : d53647 p = 1) (hb : d211114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d211092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d211092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51185 q ha hb
    | true =>
      simp only [d112, d211092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51186 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d211093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d211093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d211093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d211094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d211094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d211094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d211095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d211095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d211095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d211099 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d211099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d211099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51187 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d211100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d211100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d211100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d211101 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d211101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d211101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d211102 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d211102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d211102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d211103 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d211103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d211103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d211109 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d211109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d211109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51188 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d211110 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d211110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d211110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d211111 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d211111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d211111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d211112 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d211112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d211112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d211113 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d211113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d211113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d211114 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d211114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d211114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro51190 (p : Pattern) (ha : d209612 p = 1) (hb : d211124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209608 q = 1) (hb : d211120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209608, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209608, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209609 q = 1) (hb : d211121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209609, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209609, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209610 q = 1) (hb : d211122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209610, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209610, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209611 q = 1) (hb : d211123 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209611, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209611, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209612 q = 1) (hb : d211124 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209612, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209612, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51191 (p : Pattern) (ha : d209619 p = 1) (hb : d211129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209554 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d209608 q = 1) (hb : d211120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209608, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209608, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209609 q = 1) (hb : d211121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209609, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209609, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209610 q = 1) (hb : d211122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209610, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209610, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209611 q = 1) (hb : d211123 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209611, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209611, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23279 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23283 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d209615 q = 1) (hb : d211125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209615, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209615, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209616 q = 1) (hb : d211126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209616, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209616, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209617 q = 1) (hb : d211127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209617, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209617, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209618 q = 1) (hb : d211128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209618, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209618, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209619 q = 1) (hb : d211129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209619, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209619, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51192 (p : Pattern) (ha : d210871 p = 1) (hb : d211136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209615 q = 1) (hb : d211125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209615, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209615, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209616 q = 1) (hb : d211126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209616, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209616, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209617 q = 1) (hb : d211134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209617, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209617, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209618 q = 1) (hb : d211135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209618, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209618, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210871 q = 1) (hb : d211136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210871, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210871, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51193 (p : Pattern) (ha : d210881 p = 1) (hb : d211146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210877 q = 1) (hb : d211142 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210877, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210877, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23349 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210878 q = 1) (hb : d211143 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210878, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210878, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210879 q = 1) (hb : d211144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210879, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210879, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210880 q = 1) (hb : d211145 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210880, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210880, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210881 q = 1) (hb : d211146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210881, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210881, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51194 (p : Pattern) (ha : d210887 p = 1) (hb : d211152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209620 q = 1) (hb : d211130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209620, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51190 q ha hb
    | true =>
      simp only [d209620, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51191 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209621 q = 1) (hb : d211131 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209621, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209621, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210869 q = 1) (hb : d211132 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210869, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210869, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210870 q = 1) (hb : d211133 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210870, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210870, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210872 q = 1) (hb : d211137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210872, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210872, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51192 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d210873 q = 1) (hb : d211138 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210873, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d210873, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210874 q = 1) (hb : d211139 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210874, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210874, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d210875 q = 1) (hb : d211140 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210875, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210875, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d210876 q = 1) (hb : d211141 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210876, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d210876, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d210882 q = 1) (hb : d211147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210882, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210882, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51193 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210883 q = 1) (hb : d211148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210883, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210883, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210884 q = 1) (hb : d211149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210884, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d210884, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d210885 q = 1) (hb : d211150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210885, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d210885, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d210886 q = 1) (hb : d211151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210886, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d210886, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d210887 q = 1) (hb : d211152 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d210887, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d210887, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51195 (p : Pattern) (ha : d210893 p = 1) (hb : d211158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d211115 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51189 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d211116 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d211117 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d211118 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d211119 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210888 q = 1) (hb : d211153 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d210888, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210888, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51194 q ha hb
  have h8 (q : Pattern) (ha : d210889 q = 1) (hb : d211154 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d210889, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210889, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d210890 q = 1) (hb : d211155 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d210890, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210890, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210891 q = 1) (hb : d211156 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d210891, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210891, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d210892 q = 1) (hb : d211157 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d210892, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210892, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d210893 q = 1) (hb : d211158 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d210893, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d210893, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro51196 (p : Pattern) (ha : d209752 p = 1) (hb : d211163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209748 q = 1) (hb : d211159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209748, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209748, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209749 q = 1) (hb : d211160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209749, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209749, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209750 q = 1) (hb : d211161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209750, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209750, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209751 q = 1) (hb : d211162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209751, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209751, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209752 q = 1) (hb : d211163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209752, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209752, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51197 (p : Pattern) (ha : d209762 p = 1) (hb : d211168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d209748 q = 1) (hb : d211159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209748, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209748, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209749 q = 1) (hb : d211160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209749, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209749, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209750 q = 1) (hb : d211161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209750, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209750, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209751 q = 1) (hb : d211162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209751, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209751, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d209758 q = 1) (hb : d211164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209758, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209758, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209759 q = 1) (hb : d211165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209759, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209759, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209760 q = 1) (hb : d211166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209760, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209760, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209761 q = 1) (hb : d211167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209761, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209761, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209762 q = 1) (hb : d211168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209762, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209762, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51198 (p : Pattern) (ha : d210896 p = 1) (hb : d211175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209758 q = 1) (hb : d211164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209758, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209758, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209759 q = 1) (hb : d211165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209759, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209759, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209760 q = 1) (hb : d211173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209760, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209760, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209761 q = 1) (hb : d211174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209761, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209761, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210896 q = 1) (hb : d211175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210896, d211175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210896, d211175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51199 (p : Pattern) (ha : d210907 p = 1) (hb : d211185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210903 q = 1) (hb : d211181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210903, d211181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210903, d211181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23600 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210904 q = 1) (hb : d211182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210904, d211182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210904, d211182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210905 q = 1) (hb : d211183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210905, d211183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210905, d211183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210906 q = 1) (hb : d211184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210906, d211184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210906, d211184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210907 q = 1) (hb : d211185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210907, d211185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210907, d211185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51200 (p : Pattern) (ha : d210913 p = 1) (hb : d211191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209763 q = 1) (hb : d211169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209763, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51196 q ha hb
    | true =>
      simp only [d209763, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51197 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209764 q = 1) (hb : d211170 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209764, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209764, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210894 q = 1) (hb : d211171 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210894, d211171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210894, d211171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210895 q = 1) (hb : d211172 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210895, d211172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210895, d211172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210897 q = 1) (hb : d211176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210897, d211176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210897, d211176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51198 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d210898 q = 1) (hb : d211177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210898, d211177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d210898, d211177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210899 q = 1) (hb : d211178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210899, d211178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210899, d211178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d210900 q = 1) (hb : d211179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210900, d211179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210900, d211179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d210901 q = 1) (hb : d211180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210901, d211180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d210901, d211180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d210908 q = 1) (hb : d211186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210908, d211186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210908, d211186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51199 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23616 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210909 q = 1) (hb : d211187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210909, d211187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210909, d211187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210910 q = 1) (hb : d211188 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210910, d211188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d210910, d211188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d210911 q = 1) (hb : d211189 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210911, d211189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d210911, d211189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d210912 q = 1) (hb : d211190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210912, d211190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d210912, d211190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d210913 q = 1) (hb : d211191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d210913, d211191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d210913, d211191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51201 (p : Pattern) (ha : d210919 p = 1) (hb : d211197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210914 q = 1) (hb : d211192 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d210914, d211192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210914, d211192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51200 q ha hb
  have h2 (q : Pattern) (ha : d210915 q = 1) (hb : d211193 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d210915, d211193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210915, d211193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d210916 q = 1) (hb : d211194 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d210916, d211194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210916, d211194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d210917 q = 1) (hb : d211195 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d210917, d211195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210917, d211195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d210918 q = 1) (hb : d211196 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d210918, d211196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210918, d211196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210919 q = 1) (hb : d211197 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d210919, d211197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210919, d211197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51202 (p : Pattern) (ha : d209950 p = 1) (hb : d211203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209946 q = 1) (hb : d211199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209946, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209946, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209947 q = 1) (hb : d211200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209947, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209947, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209948 q = 1) (hb : d211201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209948, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209948, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209949 q = 1) (hb : d211202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209949, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209949, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209950 q = 1) (hb : d211203 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209950, d211203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209950, d211203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51203 (p : Pattern) (ha : d209960 p = 1) (hb : d211208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d209946 q = 1) (hb : d211199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209946, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209946, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209947 q = 1) (hb : d211200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209947, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209947, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209948 q = 1) (hb : d211201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209948, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209948, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209949 q = 1) (hb : d211202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209949, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209949, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23768 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23773 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d209956 q = 1) (hb : d211204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209956, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209956, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209957 q = 1) (hb : d211205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209957, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209957, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209958 q = 1) (hb : d211206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209958, d211206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209958, d211206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209959 q = 1) (hb : d211207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209959, d211207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209959, d211207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209960 q = 1) (hb : d211208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209960, d211208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209960, d211208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51204 (p : Pattern) (ha : d210923 p = 1) (hb : d211215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209956 q = 1) (hb : d211204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209956, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209956, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209957 q = 1) (hb : d211205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209957, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209957, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209958 q = 1) (hb : d211213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209958, d211213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209958, d211213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209959 q = 1) (hb : d211214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209959, d211214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d209959, d211214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210923 q = 1) (hb : d211215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210923, d211215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210923, d211215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51205 (p : Pattern) (ha : d210934 p = 1) (hb : d211225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210929 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210930 q = 1) (hb : d211221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210930, d211221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210930, d211221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23897 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210931 q = 1) (hb : d211222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210931, d211222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210931, d211222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210932 q = 1) (hb : d211223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210932, d211223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210932, d211223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210933 q = 1) (hb : d211224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210933, d211224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210933, d211224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210934 q = 1) (hb : d211225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210934, d211225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210934, d211225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51206 (p : Pattern) (ha : d210940 p = 1) (hb : d211231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209961 q = 1) (hb : d211209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209961, d211209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51202 q ha hb
    | true =>
      simp only [d209961, d211209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51203 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209962 q = 1) (hb : d211210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209962, d211210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209962, d211210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210921 q = 1) (hb : d211211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210921, d211211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210921, d211211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210922 q = 1) (hb : d211212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210922, d211212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210922, d211212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210924 q = 1) (hb : d211216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210924, d211216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210924, d211216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51204 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23809 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d210925 q = 1) (hb : d211217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210925, d211217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d210925, d211217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210926 q = 1) (hb : d211218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210926, d211218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210926, d211218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d210927 q = 1) (hb : d211219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210927, d211219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210927, d211219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d210928 q = 1) (hb : d211220 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210928, d211220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d210928, d211220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d210935 q = 1) (hb : d211226 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210935, d211226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210935, d211226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51205 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23913 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210936 q = 1) (hb : d211227 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210936, d211227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210936, d211227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210937 q = 1) (hb : d211228 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210937, d211228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d210937, d211228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d210938 q = 1) (hb : d211229 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210938, d211229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d210938, d211229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d210939 q = 1) (hb : d211230 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210939, d211230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d210939, d211230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d210940 q = 1) (hb : d211231 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d210940, d211231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d210940, d211231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51207 (p : Pattern) (ha : d210946 p = 1) (hb : d211237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210941 q = 1) (hb : d211232 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d210941, d211232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210941, d211232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51206 q ha hb
  have h2 (q : Pattern) (ha : d210942 q = 1) (hb : d211233 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d210942, d211233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210942, d211233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d210943 q = 1) (hb : d211234 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d210943, d211234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210943, d211234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d210944 q = 1) (hb : d211235 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d210944, d211235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210944, d211235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d210945 q = 1) (hb : d211236 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d210945, d211236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210945, d211236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210946 q = 1) (hb : d211237 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d210946, d211237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210946, d211237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51208 (p : Pattern) (ha : d210168 p = 1) (hb : d211244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210164 q = 1) (hb : d211240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210164, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210164, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d210165 q = 1) (hb : d211241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210165, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d210165, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210166 q = 1) (hb : d211242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210166, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d210166, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d210167 q = 1) (hb : d211243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210167, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210167, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210168 q = 1) (hb : d211244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210168, d211244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210168, d211244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51209 (p : Pattern) (ha : d210178 p = 1) (hb : d211249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d210163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d210164 q = 1) (hb : d211240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210164, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d210164, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d210165 q = 1) (hb : d211241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210165, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210165, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210166 q = 1) (hb : d211242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210166, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210166, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210167 q = 1) (hb : d211243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210167, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210167, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24115 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24120 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d210174 q = 1) (hb : d211245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210174, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d210174, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210175 q = 1) (hb : d211246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210175, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210175, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210176 q = 1) (hb : d211247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210176, d211247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210176, d211247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d210177 q = 1) (hb : d211248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210177, d211248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210177, d211248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d210178 q = 1) (hb : d211249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210178, d211249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d210178, d211249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51210 (p : Pattern) (ha : d210951 p = 1) (hb : d211256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210174 q = 1) (hb : d211245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210174, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210174, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210175 q = 1) (hb : d211246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210175, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210175, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210176 q = 1) (hb : d211254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210176, d211254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210176, d211254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210177 q = 1) (hb : d211255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210177, d211255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210177, d211255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210951 q = 1) (hb : d211256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210951, d211256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210951, d211256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51211 (p : Pattern) (ha : d210962 p = 1) (hb : d211266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24217 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210958 q = 1) (hb : d211262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210958, d211262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210958, d211262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210959 q = 1) (hb : d211263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210959, d211263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210959, d211263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210960 q = 1) (hb : d211264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210960, d211264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210960, d211264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210961 q = 1) (hb : d211265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210961, d211265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210961, d211265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210962 q = 1) (hb : d211266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210962, d211266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210962, d211266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51212 (p : Pattern) (ha : d210968 p = 1) (hb : d211272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210179 q = 1) (hb : d211250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210179, d211250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51208 q ha hb
    | true =>
      simp only [d210179, d211250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51209 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24147 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210180 q = 1) (hb : d211251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210180, d211251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210180, d211251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210949 q = 1) (hb : d211252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210949, d211252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210949, d211252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210950 q = 1) (hb : d211253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210950, d211253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210950, d211253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210952 q = 1) (hb : d211257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210952, d211257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210952, d211257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51210 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24156 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d210953 q = 1) (hb : d211258 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210953, d211258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d210953, d211258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210954 q = 1) (hb : d211259 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210954, d211259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210954, d211259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d210955 q = 1) (hb : d211260 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210955, d211260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210955, d211260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d210956 q = 1) (hb : d211261 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210956, d211261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d210956, d211261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d210963 q = 1) (hb : d211267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210963, d211267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210963, d211267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51211 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24292 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210964 q = 1) (hb : d211268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210964, d211268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210964, d211268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210965 q = 1) (hb : d211269 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210965, d211269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d210965, d211269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d210966 q = 1) (hb : d211270 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210966, d211270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d210966, d211270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d210967 q = 1) (hb : d211271 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210967, d211271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d210967, d211271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d210968 q = 1) (hb : d211272 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d210968, d211272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d210968, d211272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51213 (p : Pattern) (ha : d210974 p = 1) (hb : d211278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210969 q = 1) (hb : d211273 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d210969, d211273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210969, d211273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51212 q ha hb
  have h2 (q : Pattern) (ha : d210970 q = 1) (hb : d211274 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d210970, d211274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210970, d211274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d210971 q = 1) (hb : d211275 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d210971, d211275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210971, d211275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d210972 q = 1) (hb : d211276 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d210972, d211276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210972, d211276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d210973 q = 1) (hb : d211277 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d210973, d211277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210973, d211277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210974 q = 1) (hb : d211278 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d210974, d211278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210974, d211278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51214 (p : Pattern) (ha : d210411 p = 1) (hb : d211286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210407 q = 1) (hb : d211282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210407, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210407, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d210408 q = 1) (hb : d211283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210408, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d210408, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210409 q = 1) (hb : d211284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210409, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d210409, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d210410 q = 1) (hb : d211285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210410, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210410, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210411 q = 1) (hb : d211286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210411, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210411, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51215 (p : Pattern) (ha : d210421 p = 1) (hb : d211291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d210406 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d210407 q = 1) (hb : d211282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210407, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d210407, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d210408 q = 1) (hb : d211283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210408, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210408, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210409 q = 1) (hb : d211284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210409, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210409, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210410 q = 1) (hb : d211285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210410, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210410, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24502 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d210417 q = 1) (hb : d211287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210417, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d210417, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210418 q = 1) (hb : d211288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210418, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210418, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210419 q = 1) (hb : d211289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210419, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210419, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d210420 q = 1) (hb : d211290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210420, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210420, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d210421 q = 1) (hb : d211291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210421, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d210421, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51216 (p : Pattern) (ha : d210980 p = 1) (hb : d211298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210417 q = 1) (hb : d211287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210417, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210417, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210418 q = 1) (hb : d211288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210418, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210418, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210419 q = 1) (hb : d211296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210419, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210419, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210420 q = 1) (hb : d211297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210420, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210420, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210980 q = 1) (hb : d211298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210980, d211298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210980, d211298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51217 (p : Pattern) (ha : d210991 p = 1) (hb : d211308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210987 q = 1) (hb : d211304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210987, d211304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210987, d211304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24658 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210988 q = 1) (hb : d211305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210988, d211305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210988, d211305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210989 q = 1) (hb : d211306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210989, d211306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210989, d211306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210990 q = 1) (hb : d211307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210990, d211307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210990, d211307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210991 q = 1) (hb : d211308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210991, d211308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210991, d211308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51218 (p : Pattern) (ha : d210997 p = 1) (hb : d211314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210422 q = 1) (hb : d211292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210422, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51214 q ha hb
    | true =>
      simp only [d210422, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51215 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210423 q = 1) (hb : d211293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210423, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210423, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210978 q = 1) (hb : d211294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210978, d211294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210978, d211294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210979 q = 1) (hb : d211295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210979, d211295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210979, d211295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210981 q = 1) (hb : d211299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210981, d211299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210981, d211299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51216 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24538 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d210982 q = 1) (hb : d211300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210982, d211300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d210982, d211300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210983 q = 1) (hb : d211301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210983, d211301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210983, d211301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d210984 q = 1) (hb : d211302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210984, d211302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210984, d211302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d210985 q = 1) (hb : d211303 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210985, d211303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d210985, d211303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d210992 q = 1) (hb : d211309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210992, d211309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210992, d211309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51217 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24674 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210993 q = 1) (hb : d211310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210993, d211310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210993, d211310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210994 q = 1) (hb : d211311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d210994, d211311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d210994, d211311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d210995 q = 1) (hb : d211312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d210995, d211312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d210995, d211312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d210996 q = 1) (hb : d211313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d210996, d211313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d210996, d211313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d210997 q = 1) (hb : d211314 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d210997, d211314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d210997, d211314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51219 (p : Pattern) (ha : d211003 p = 1) (hb : d211320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210998 q = 1) (hb : d211315 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d210998, d211315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210998, d211315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51218 q ha hb
  have h2 (q : Pattern) (ha : d210999 q = 1) (hb : d211316 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d210999, d211316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210999, d211316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211000 q = 1) (hb : d211317 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211000, d211317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211000, d211317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211001 q = 1) (hb : d211318 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211001, d211318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211001, d211318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211002 q = 1) (hb : d211319 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211002, d211319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211002, d211319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211003 q = 1) (hb : d211320 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211003, d211320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211003, d211320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51220 (p : Pattern) (ha : d210643 p = 1) (hb : d211329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210639 q = 1) (hb : d211325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210639, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210639, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d210640 q = 1) (hb : d211326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210640, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d210640, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210641 q = 1) (hb : d211327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210641, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d210641, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d210642 q = 1) (hb : d211328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210642, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210642, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d210643 q = 1) (hb : d211329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210643, d211329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210643, d211329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51221 (p : Pattern) (ha : d210653 p = 1) (hb : d211334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d210638 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d210639 q = 1) (hb : d211325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210639, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d210639, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d210640 q = 1) (hb : d211326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210640, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d210640, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210641 q = 1) (hb : d211327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210641, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210641, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d210642 q = 1) (hb : d211328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210642, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210642, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24874 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d210649 q = 1) (hb : d211330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210649, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d210649, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d210650 q = 1) (hb : d211331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210650, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d210650, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d210651 q = 1) (hb : d211332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210651, d211332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d210651, d211332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d210652 q = 1) (hb : d211333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210652, d211333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d210652, d211333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d210653 q = 1) (hb : d211334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d210653, d211334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d210653, d211334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro51222 (p : Pattern) (ha : d211010 p = 1) (hb : d211341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d210648 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210649 q = 1) (hb : d211330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d210649, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210649, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d210650 q = 1) (hb : d211331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d210650, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210650, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210651 q = 1) (hb : d211339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d210651, d211339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210651, d211339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d210652 q = 1) (hb : d211340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d210652, d211340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210652, d211340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211010 q = 1) (hb : d211341 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211010, d211341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211010, d211341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51223 (p : Pattern) (ha : d211021 p = 1) (hb : d211351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211016 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211017 q = 1) (hb : d211347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211017, d211347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211017, d211347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211018 q = 1) (hb : d211348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211018, d211348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211018, d211348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211019 q = 1) (hb : d211349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211019, d211349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211019, d211349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211020 q = 1) (hb : d211350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211020, d211350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211020, d211350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211021 q = 1) (hb : d211351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211021, d211351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211021, d211351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51224 (p : Pattern) (ha : d211027 p = 1) (hb : d211357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24759 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d210654 q = 1) (hb : d211335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d210654, d211335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51220 q ha hb
    | true =>
      simp only [d210654, d211335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51221 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d210655 q = 1) (hb : d211336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d210655, d211336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210655, d211336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211008 q = 1) (hb : d211337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211008, d211337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211008, d211337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211009 q = 1) (hb : d211338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211009, d211338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211009, d211338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211011 q = 1) (hb : d211342 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211011, d211342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211011, d211342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51222 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24910 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211012 q = 1) (hb : d211343 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211012, d211343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211012, d211343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211013 q = 1) (hb : d211344 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211013, d211344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211013, d211344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211014 q = 1) (hb : d211345 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211014, d211345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211014, d211345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211015 q = 1) (hb : d211346 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211015, d211346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211015, d211346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211022 q = 1) (hb : d211352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211022, d211352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211022, d211352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51223 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25042 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211023 q = 1) (hb : d211353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211023, d211353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211023, d211353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d211024 q = 1) (hb : d211354 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211024, d211354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211024, d211354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211025 q = 1) (hb : d211355 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211025, d211355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211025, d211355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211026 q = 1) (hb : d211356 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211026, d211356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211026, d211356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211027 q = 1) (hb : d211357 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211027, d211357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211027, d211357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51225 (p : Pattern) (ha : d211033 p = 1) (hb : d211363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211028 q = 1) (hb : d211358 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211028, d211358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211028, d211358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51224 q ha hb
  have h2 (q : Pattern) (ha : d211029 q = 1) (hb : d211359 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211029, d211359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211029, d211359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211030 q = 1) (hb : d211360 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211030, d211360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211030, d211360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211031 q = 1) (hb : d211361 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211031, d211361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211031, d211361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211032 q = 1) (hb : d211362 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211032, d211362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211032, d211362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211033 q = 1) (hb : d211363 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211033, d211363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211033, d211363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51226 (p : Pattern) (ha : d211039 p = 1) (hb : d211369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d210920 q = 1) (hb : d211198 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d210920, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51195 q ha hb
    | true =>
      simp only [d210920, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51201 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d210947 q = 1) (hb : d211238 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d210947, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210947, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51207 q ha hb
  have h3 (q : Pattern) (ha : d210948 q = 1) (hb : d211239 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d210948, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d210948, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d210975 q = 1) (hb : d211279 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d210975, d211279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210975, d211279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51213 q ha hb
  have h5 (q : Pattern) (ha : d210976 q = 1) (hb : d211280 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d210976, d211280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d210976, d211280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d210977 q = 1) (hb : d211281 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d210977, d211281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d210977, d211281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211004 q = 1) (hb : d211321 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211004, d211321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211004, d211321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51219 q ha hb
  have h8 (q : Pattern) (ha : d211005 q = 1) (hb : d211322 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211005, d211322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211005, d211322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211006 q = 1) (hb : d211323 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211006, d211323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211006, d211323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211007 q = 1) (hb : d211324 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211007, d211324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211007, d211324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211034 q = 1) (hb : d211364 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211034, d211364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211034, d211364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51225 q ha hb
  have h12 (q : Pattern) (ha : d211035 q = 1) (hb : d211365 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211035, d211365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211035, d211365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211036 q = 1) (hb : d211366 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211036, d211366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211036, d211366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211037 q = 1) (hb : d211367 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211037, d211367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211037, d211367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211038 q = 1) (hb : d211368 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d211038, d211368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211038, d211368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d211039 q = 1) (hb : d211369 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d211039, d211369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211039, d211369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro51227 (p : Pattern) (ha : d211045 p = 1) (hb : d211375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211040 q = 1) (hb : d211370 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d211040, d211370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51226 q ha hb
    | true =>
      simp only [d211040, d211370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211041 q = 1) (hb : d211371 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d211041, d211371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211041, d211371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211042 q = 1) (hb : d211372 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d211042, d211372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211042, d211372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211043 q = 1) (hb : d211373 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d211043, d211373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211043, d211373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211044 q = 1) (hb : d211374 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d211044, d211374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211044, d211374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211045 q = 1) (hb : d211375 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d211045, d211375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211045, d211375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51228 (p : Pattern) (ha : d211051 p = 1) (hb : d211381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211046 q = 1) (hb : d211376 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d211046, d211376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51227 q ha hb
    | true =>
      simp only [d211046, d211376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211047 q = 1) (hb : d211377 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d211047, d211377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211047, d211377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211048 q = 1) (hb : d211378 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d211048, d211378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211048, d211378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211049 q = 1) (hb : d211379 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d211049, d211379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211049, d211379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211050 q = 1) (hb : d211380 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d211050, d211380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211050, d211380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211051 q = 1) (hb : d211381 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d211051, d211381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211051, d211381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51229 (p : Pattern) (ha : d211057 p = 1) (hb : d211387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211052 q = 1) (hb : d211382 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d211052, d211382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51228 q ha hb
    | true =>
      simp only [d211052, d211382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211053 q = 1) (hb : d211383 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d211053, d211383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211053, d211383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211054 q = 1) (hb : d211384 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d211054, d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211054, d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211055 q = 1) (hb : d211385 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d211055, d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211055, d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211056 q = 1) (hb : d211386 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d211056, d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211056, d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211057 q = 1) (hb : d211387 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d211057, d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211057, d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51230 (p : Pattern) (ha : d211063 p = 1) (hb : d211393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211058 q = 1) (hb : d211388 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d211058, d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51229 q ha hb
    | true =>
      simp only [d211058, d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211059 q = 1) (hb : d211389 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d211059, d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211059, d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211060 q = 1) (hb : d211390 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d211060, d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211060, d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211061 q = 1) (hb : d211391 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d211061, d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211061, d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211062 q = 1) (hb : d211392 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d211062, d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211062, d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211063 q = 1) (hb : d211393 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d211063, d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211063, d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51231 (p : Pattern) (ha : d211069 p = 1) (hb : d211399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211064 q = 1) (hb : d211394 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d211064, d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51230 q ha hb
    | true =>
      simp only [d211064, d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211065 q = 1) (hb : d211395 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d211065, d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211065, d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211066 q = 1) (hb : d211396 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d211066, d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211066, d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211067 q = 1) (hb : d211397 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d211067, d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211067, d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211068 q = 1) (hb : d211398 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d211068, d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211068, d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211069 q = 1) (hb : d211399 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d211069, d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211069, d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51232 (p : Pattern) (ha : d211075 p = 1) (hb : d211405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211070 q = 1) (hb : d211400 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d211070, d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51231 q ha hb
    | true =>
      simp only [d211070, d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211071 q = 1) (hb : d211401 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d211071, d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211071, d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211072 q = 1) (hb : d211402 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d211072, d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211072, d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211073 q = 1) (hb : d211403 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d211073, d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211073, d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211074 q = 1) (hb : d211404 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d211074, d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211074, d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211075 q = 1) (hb : d211405 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d211075, d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211075, d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51233 (p : Pattern) (ha : d211081 p = 1) (hb : d211411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211076 q = 1) (hb : d211406 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d211076, d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51232 q ha hb
    | true =>
      simp only [d211076, d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211077 q = 1) (hb : d211407 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d211077, d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211077, d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211078 q = 1) (hb : d211408 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d211078, d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211078, d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211079 q = 1) (hb : d211409 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d211079, d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211079, d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211080 q = 1) (hb : d211410 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d211080, d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211080, d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211081 q = 1) (hb : d211411 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d211081, d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211081, d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51234 (p : Pattern) (ha : d144 p = 1) (hb : d122304 p = 1) : d13981 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d142 q = 1) : d142 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d143 q = 1) (hb : d122304 q = 1) : d13980 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d29 q = 1) (hb : d122304 q = 1) : d29 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144 q = 1) (hb : d122304 q = 1) : d13981 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d13981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144, d13981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro51235 (p : Pattern) (ha : d150 p = 1) (hb : d122304 p = 1) : d13987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122304 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d122304 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51234 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d122304 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d122304 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d122304 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d122304 q = 1) : d13985 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d122304 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d122304 q = 1) : d13986 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d122304 q = 1) : d13987 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro51236 (p : Pattern) (ha : d203 p = 1) (hb : d122304 p = 1) : d14000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d122304 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51235 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d122304 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122304 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d122304 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d122304 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d122304 q = 1) : d13992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d122304 q = 1) : d14000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51237 (p : Pattern) (ha : d4349 p = 1) (hb : d122304 p = 1) : d125429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122304 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d122304 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51236 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d122304 q = 1) : d125418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d122304 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d122304 q = 1) : d125419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d122304 q = 1) : d125427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d122304 q = 1) : d125428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d122304 q = 1) : d125429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51238 (p : Pattern) (ha : d231 p = 1) (hb : d122304 p = 1) : d14020 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d229 q = 1) : d229 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d230 q = 1) (hb : d122304 q = 1) : d14019 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70 q = 1) (hb : d122304 q = 1) : d70 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d231 q = 1) (hb : d122304 q = 1) : d14020 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d14020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231, d14020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro51239 (p : Pattern) (ha : d237 p = 1) (hb : d122304 p = 1) : d14026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122304 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d122304 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51238 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d122304 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d122304 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d122304 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d122304 q = 1) : d14024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d122304 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d122304 q = 1) : d14025 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d122304 q = 1) : d14026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro51240 (p : Pattern) (ha : d243 p = 1) (hb : d122304 p = 1) : d14032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d122304 q = 1) : d14027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51239 q ha hb
    | true =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d122304 q = 1) : d14028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d122304 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d122304 q = 1) : d14029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d122304 q = 1) : d14030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d122304 q = 1) : d14031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d122304 q = 1) : d14032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51241 (p : Pattern) (ha : d4359 p = 1) (hb : d122304 p = 1) : d125439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122304 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d122304 q = 1) : d14033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51240 q ha hb
    | true =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d122304 q = 1) : d125435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d122304 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d122304 q = 1) : d125436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d122304 q = 1) : d125437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d122304 q = 1) : d125438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d122304 q = 1) : d125439 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51242 (p : Pattern) (ha : d156 p = 1) (hb : d122304 p = 1) : d13993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d122304 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51235 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d122304 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122304 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d122304 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d122304 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d122304 q = 1) : d13992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d122304 q = 1) : d13993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51243 (p : Pattern) (ha : d51643 p = 1) (hb : d122304 p = 1) : d125417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d122304 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d122304 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d122304 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d122304 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51242 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d122304 q = 1) : d125413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122304 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d122304 q = 1) : d125414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d122304 q = 1) : d125415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d122304 q = 1) : d125416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d122304 q = 1) : d125417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51244 (p : Pattern) (ha : d51646 p = 1) (hb : d122304 p = 1) : d125422 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d122304 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d122304 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d122304 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d122304 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51242 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d122304 q = 1) : d125413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122304 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d122304 q = 1) : d125414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d122304 q = 1) : d125415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d122304 q = 1) : d125416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d122304 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d122304 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d122304 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d122304 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51236 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d122304 q = 1) : d125418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d122304 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d122304 q = 1) : d125419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d122304 q = 1) : d125420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d122304 q = 1) : d125421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d122304 q = 1) : d125422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51245 (p : Pattern) (ha : d51652 p = 1) (hb : d122304 p = 1) : d125445 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d122304 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d122304 q = 1) : d125423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51243 q ha hb
    | true =>
      simp only [d51647, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51244 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d122304 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d122304 q = 1) : d125424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d122304 q = 1) : d125425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d122304 q = 1) : d125426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d122304 q = 1) : d125430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51237 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d122304 q = 1) : d125431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d122304 q = 1) : d125432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d122304 q = 1) : d125433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d122304 q = 1) : d125434 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d122304 q = 1) : d125440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51241 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d122304 q = 1) : d125441 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d122304 q = 1) : d125442 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d122304 q = 1) : d125443 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d122304 q = 1) : d125444 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d122304 q = 1) : d125445 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro51246 (p : Pattern) (ha : d284 p = 1) (hb : d122304 p = 1) : d14054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122304 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d122304 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51242 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d122304 q = 1) : d14050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d122304 q = 1) : d14051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d122304 q = 1) : d14052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d122304 q = 1) : d14053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d122304 q = 1) : d14054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51247 (p : Pattern) (ha : d291 p = 1) (hb : d122304 p = 1) : d14061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122304 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d122304 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51242 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d122304 q = 1) : d14050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d122304 q = 1) : d14051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d122304 q = 1) : d14052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d122304 q = 1) : d14053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d122304 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d122304 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51236 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d122304 q = 1) : d14057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d122304 q = 1) : d14058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d122304 q = 1) : d14059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d122304 q = 1) : d14060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d122304 q = 1) : d14061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro51248 (p : Pattern) (ha : d397 p = 1) (hb : d122304 p = 1) : d14141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122304 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d122304 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51242 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d122304 q = 1) : d14050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d122304 q = 1) : d14051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d122304 q = 1) : d14052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d122304 q = 1) : d14053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d122304 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d122304 q = 1) : d14141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51249 (p : Pattern) (ha : d296 p = 1) (hb : d122304 p = 1) : d14066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d122304 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51235 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d122304 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122304 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d122304 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d122304 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d122304 q = 1) : d14065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d122304 q = 1) : d14066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
