import NetHack.Soko22Hazard87.AndIntroBlocks0399
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro100000 (p : Pattern) (ha : d44444 p = 1) (hb : d362516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d362510 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d362510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d362510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99999 q ha hb
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d362511 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d362511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, d362511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99998 q ha hb
  have h3 (q : Pattern) (ha : d35373 q = 1) (hb : d362512 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d362512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d362512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44441 q = 1) (hb : d362513 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d362513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, d362513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44442 q = 1) (hb : d362514 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d362514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, d362514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44443 q = 1) (hb : d362515 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d362515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, d362515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44444 q = 1) (hb : d362516 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44444, d362516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44444, d362516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100001 (p : Pattern) (ha : d1563 p = 1) (hb : d361193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1531 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1547 q = 1) (hb : d361192 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d361192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1547, d361192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1563 q = 1) (hb : d361193 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1563, d361193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1563, d361193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h6 p ha hb
theorem andIntro100002 (p : Pattern) (ha : d44450 p = 1) (hb : d362523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34366 q = 1) (hb : d361896 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, d361896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34366, d361896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34367 q = 1) (hb : d362522 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d34367, d362522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34367, d362522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44450 q = 1) (hb : d362523 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44450, d362523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44450, d362523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100003 (p : Pattern) (ha : d44459 p = 1) (hb : d362532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d362510 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d362510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d362510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99999 q ha hb
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d362511 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d362511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, d362511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99998 q ha hb
  have h3 (q : Pattern) (ha : d35373 q = 1) (hb : d362512 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d362512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d362512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44441 q = 1) (hb : d362513 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d362513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, d362513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44442 q = 1) (hb : d362514 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d362514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, d362514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44443 q = 1) (hb : d362515 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d362515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, d362515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44451 q = 1) (hb : d362524 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, d362524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44451, d362524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100002 q ha hb
  have h8 (q : Pattern) (ha : d5128 q = 1) (hb : d362141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h9 (q : Pattern) (ha : d44452 q = 1) (hb : d362525 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, d362525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44452, d362525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44453 q = 1) (hb : d362526 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, d362526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44453, d362526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44454 q = 1) (hb : d362527 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, d362527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100002 q ha hb
    | true =>
      simp only [d44454, d362527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44455 q = 1) (hb : d362528 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, d362528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44455, d362528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44456 q = 1) (hb : d362529 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, d362529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44456, d362529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44457 q = 1) (hb : d362530 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, d362530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44457, d362530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44458 q = 1) (hb : d362531 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, d362531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44458, d362531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d44459 q = 1) (hb : d362532 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44459, d362532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44459, d362532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro100004 (p : Pattern) (ha : d44465 p = 1) (hb : d362538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d362519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d362520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44449 q = 1) (hb : d362521 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, d362521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44449, d362521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44462 q = 1) (hb : d362535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44463 q = 1) (hb : d362536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44464 q = 1) (hb : d362537 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d362537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d362537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44465 q = 1) (hb : d362538 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44465, d362538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44465, d362538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100005 (p : Pattern) (ha : d44467 p = 1) (hb : d362540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d362519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d362520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d362535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d362536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d362537 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d362537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d362537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44466 q = 1) (hb : d362539 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d362539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44466, d362539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44467 q = 1) (hb : d362540 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44467, d362540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44467, d362540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100006 (p : Pattern) (ha : d44471 p = 1) (hb : d362544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44451 q = 1) (hb : d362524 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, d362524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44451, d362524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100002 q ha hb
  have h2 (q : Pattern) (ha : d5128 q = 1) (hb : d362141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h3 (q : Pattern) (ha : d44452 q = 1) (hb : d362525 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, d362525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44452, d362525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44453 q = 1) (hb : d362526 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, d362526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44453, d362526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44454 q = 1) (hb : d362527 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, d362527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100002 q ha hb
    | true =>
      simp only [d44454, d362527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44455 q = 1) (hb : d362528 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, d362528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44455, d362528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44456 q = 1) (hb : d362529 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, d362529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44456, d362529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44457 q = 1) (hb : d362530 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, d362530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44457, d362530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44458 q = 1) (hb : d362531 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, d362531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44458, d362531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44471 q = 1) (hb : d362544 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44471, d362544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44471, d362544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro100007 (p : Pattern) (ha : d44477 p = 1) (hb : d362550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44462 q = 1) (hb : d362535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44463 q = 1) (hb : d362536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44466 q = 1) (hb : d362539 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d362539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44466, d362539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44472 q = 1) (hb : d362545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, d362545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100006 q ha hb
    | true =>
      simp only [d44472, d362545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44473 q = 1) (hb : d362546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, d362546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44473, d362546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44474 q = 1) (hb : d362547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44474, d362547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44474, d362547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44475 q = 1) (hb : d362548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44475, d362548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44475, d362548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44476 q = 1) (hb : d362549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44476, d362549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44476, d362549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44477 q = 1) (hb : d362550 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44477, d362550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44477, d362550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100008 (p : Pattern) (ha : d44484 p = 1) (hb : d362557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44468 q = 1) (hb : d362541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d362541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100004 q ha hb
    | true =>
      simp only [d44468, d362541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
  have h2 (q : Pattern) (ha : d44469 q = 1) (hb : d362542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d362542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d362542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44470 q = 1) (hb : d362543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d362543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d362543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44478 q = 1) (hb : d362551 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
    | true =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100007 q ha hb
  have h5 (q : Pattern) (ha : d44479 q = 1) (hb : d362552 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44480 q = 1) (hb : d362553 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44481 q = 1) (hb : d362554 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d362554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, d362554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44482 q = 1) (hb : d362555 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, d362555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44482, d362555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44483 q = 1) (hb : d362556 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44483, d362556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44483, d362556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44484 q = 1) (hb : d362557 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44484, d362557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44484, d362557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro100009 (p : Pattern) (ha : d44488 p = 1) (hb : d362561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44478 q = 1) (hb : d362551 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
    | true =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100007 q ha hb
  have h2 (q : Pattern) (ha : d44479 q = 1) (hb : d362552 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44480 q = 1) (hb : d362553 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44482 q = 1) (hb : d362555 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, d362555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44482, d362555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44487 q = 1) (hb : d362560 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44487, d362560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44487, d362560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44488 q = 1) (hb : d362561 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44488, d362561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44488, d362561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100010 (p : Pattern) (ha : d44494 p = 1) (hb : d362567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d362564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d362565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44493 q = 1) (hb : d362566 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, d362566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, d362566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44494 q = 1) (hb : d362567 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44494, d362567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44494, d362567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100011 (p : Pattern) (ha : d44498 p = 1) (hb : d362571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d362568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d362569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44497 q = 1) (hb : d362570 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, d362570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, d362570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44498 q = 1) (hb : d362571 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44498, d362571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44498, d362571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100012 (p : Pattern) (ha : d44504 p = 1) (hb : d362577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
    | true =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d362573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d362573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d362573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d362574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d362574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d362574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d362575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d362575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d362575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d362576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d362576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d362576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44504 q = 1) (hb : d362577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d362577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d362577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100013 (p : Pattern) (ha : d44507 p = 1) (hb : d362580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d362564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d362565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44493 q = 1) (hb : d362566 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, d362566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, d362566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44507 q = 1) (hb : d362580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44507, d362580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44507, d362580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100014 (p : Pattern) (ha : d44508 p = 1) (hb : d362581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d362568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d362569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44497 q = 1) (hb : d362570 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, d362570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, d362570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44508 q = 1) (hb : d362581 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44508, d362581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44508, d362581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100015 (p : Pattern) (ha : d44514 p = 1) (hb : d362587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
    | true =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d362573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d362573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d362573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d362574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d362574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d362574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d362575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d362575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d362575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d362576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d362576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d362576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44509 q = 1) (hb : d362582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d362582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100013 q ha hb
    | true =>
      simp only [d44509, d362582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100014 q ha hb
  have h7 (q : Pattern) (ha : d44510 q = 1) (hb : d362583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d362583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44510, d362583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44511 q = 1) (hb : d362584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d362584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44511, d362584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44512 q = 1) (hb : d362585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d362585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d362585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44513 q = 1) (hb : d362586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d362586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d362586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44514 q = 1) (hb : d362587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d362587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44514, d362587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100016 (p : Pattern) (ha : d44665 p = 1) (hb : d362676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
    | true =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d362573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d362573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d362573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d362574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d362574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d362574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d362575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d362575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d362575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d362576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d362576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d362576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44660 q = 1) (hb : d362671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, d362671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
    | true =>
      simp only [d44660, d362671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44661 q = 1) (hb : d362672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, d362672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44661, d362672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44662 q = 1) (hb : d362673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, d362673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44662, d362673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44663 q = 1) (hb : d362674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, d362674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44663, d362674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44664 q = 1) (hb : d362675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, d362675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44664, d362675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44665 q = 1) (hb : d362676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44665, d362676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44665, d362676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100017 (p : Pattern) (ha : d44671 p = 1) (hb : d362682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44660 q = 1) (hb : d362671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, d362671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
    | true =>
      simp only [d44660, d362671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44661 q = 1) (hb : d362672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, d362672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44661, d362672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44662 q = 1) (hb : d362673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, d362673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44662, d362673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44663 q = 1) (hb : d362674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, d362674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44663, d362674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44664 q = 1) (hb : d362675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, d362675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44664, d362675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44666 q = 1) (hb : d362677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, d362677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100014 q ha hb
    | true =>
      simp only [d44666, d362677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44667 q = 1) (hb : d362678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, d362678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44667, d362678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44668 q = 1) (hb : d362679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, d362679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44668, d362679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44669 q = 1) (hb : d362680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, d362680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44669, d362680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44670 q = 1) (hb : d362681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, d362681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44670, d362681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44671 q = 1) (hb : d362682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44671, d362682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44671, d362682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100018 (p : Pattern) (ha : d44680 p = 1) (hb : d362691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44666 q = 1) (hb : d362677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, d362677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100014 q ha hb
    | true =>
      simp only [d44666, d362677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44667 q = 1) (hb : d362678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, d362678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44667, d362678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44668 q = 1) (hb : d362679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, d362679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44668, d362679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44669 q = 1) (hb : d362680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, d362680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44669, d362680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44670 q = 1) (hb : d362681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, d362681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44670, d362681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44680 q = 1) (hb : d362691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44680, d362691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44680, d362691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100019 (p : Pattern) (ha : d44702 p = 1) (hb : d362713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d362697 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d362698 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d362699 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d362700 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d362703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d362704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d362705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d362706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d362707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d362707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d362707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44701 q = 1) (hb : d362712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d362712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44701, d362712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44702 q = 1) (hb : d362713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44702, d362713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44702, d362713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100020 (p : Pattern) (ha : d44712 p = 1) (hb : d362723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44692 q = 1) (hb : d362703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
  have h2 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44693 q = 1) (hb : d362704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44694 q = 1) (hb : d362705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44695 q = 1) (hb : d362706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44701 q = 1) (hb : d362712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d362712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44701, d362712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44707 q = 1) (hb : d362718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44707, d362718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44707, d362718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100006 q ha hb
  have h9 (q : Pattern) (ha : d44472 q = 1) (hb : d362545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, d362545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100006 q ha hb
    | true =>
      simp only [d44472, d362545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44708 q = 1) (hb : d362719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44708, d362719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44708, d362719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44473 q = 1) (hb : d362546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, d362546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44473, d362546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44709 q = 1) (hb : d362720 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44709, d362720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44709, d362720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44710 q = 1) (hb : d362721 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44710, d362721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44710, d362721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44711 q = 1) (hb : d362722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44711, d362722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44711, d362722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44712 q = 1) (hb : d362723 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44712, d362723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44712, d362723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100021 (p : Pattern) (ha : d44731 p = 1) (hb : d362742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44713 q = 1) (hb : d362724 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
    | true =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100020 q ha hb
  have h2 (q : Pattern) (ha : d44714 q = 1) (hb : d362725 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44715 q = 1) (hb : d362726 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44721 q = 1) (hb : d362732 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d362732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44721, d362732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44730 q = 1) (hb : d362741 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44730, d362741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44730, d362741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44731 q = 1) (hb : d362742 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44731, d362742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44731, d362742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100022 (p : Pattern) (ha : d44813 p = 1) (hb : d362753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44732 q = 1) (hb : d362743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d362743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100021 q ha hb
    | true =>
      simp only [d44732, d362743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44733 q = 1) (hb : d362744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d362744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d362744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44810 q = 1) (hb : d362750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44810, d362750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44810, d362750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44811 q = 1) (hb : d362751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44811, d362751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44811, d362751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44812 q = 1) (hb : d362752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44812, d362752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44812, d362752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44813 q = 1) (hb : d362753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44813, d362753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44813, d362753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100023 (p : Pattern) (ha : d44819 p = 1) (hb : d362787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44814 q = 1) (hb : d362782 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44814, d362782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100022 q ha hb
    | true =>
      simp only [d44814, d362782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44815 q = 1) (hb : d362783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44815, d362783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44815, d362783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44816 q = 1) (hb : d362784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44816, d362784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44816, d362784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44817 q = 1) (hb : d362785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44817, d362785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44817, d362785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44818 q = 1) (hb : d362786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44818, d362786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44818, d362786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44819 q = 1) (hb : d362787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44819, d362787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44819, d362787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100024 (p : Pattern) (ha : d44519 p = 1) (hb : d362592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d362564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d362565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44518 q = 1) (hb : d362591 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, d362591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44518, d362591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44519 q = 1) (hb : d362592 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44519, d362592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44519, d362592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100025 (p : Pattern) (ha : d44521 p = 1) (hb : d362594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d362568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d362569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44520 q = 1) (hb : d362593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, d362593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44520, d362593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44521 q = 1) (hb : d362594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44521, d362594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44521, d362594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100026 (p : Pattern) (ha : d44528 p = 1) (hb : d362601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d362564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44526 q = 1) (hb : d362599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, d362599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44526, d362599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44527 q = 1) (hb : d362600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, d362600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, d362600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44528 q = 1) (hb : d362601 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44528, d362601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44528, d362601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100027 (p : Pattern) (ha : d44531 p = 1) (hb : d362604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d362568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44529 q = 1) (hb : d362602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, d362602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44529, d362602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44530 q = 1) (hb : d362603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, d362603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, d362603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44531 q = 1) (hb : d362604 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44531, d362604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44531, d362604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100028 (p : Pattern) (ha : d44535 p = 1) (hb : d362608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d362519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d362520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44449 q = 1) (hb : d362521 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, d362521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44449, d362521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44535 q = 1) (hb : d362608 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44535, d362608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44535, d362608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100029 (p : Pattern) (ha : d44541 p = 1) (hb : d362614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44536 q = 1) (hb : d362609 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44536, d362609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100028 q ha hb
    | true =>
      simp only [d44536, d362609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100004 q ha hb
  have h2 (q : Pattern) (ha : d44537 q = 1) (hb : d362610 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44537, d362610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44537, d362610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44538 q = 1) (hb : d362611 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44538, d362611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44538, d362611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44468 q = 1) (hb : d362541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d362541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100004 q ha hb
    | true =>
      simp only [d44468, d362541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
  have h5 (q : Pattern) (ha : d44469 q = 1) (hb : d362542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d362542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d362542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44470 q = 1) (hb : d362543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d362543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d362543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44539 q = 1) (hb : d362612 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44539, d362612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44539, d362612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44478 q = 1) (hb : d362551 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
    | true =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100007 q ha hb
  have h9 (q : Pattern) (ha : d44479 q = 1) (hb : d362552 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44480 q = 1) (hb : d362553 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44481 q = 1) (hb : d362554 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d362554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44481, d362554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44540 q = 1) (hb : d362613 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44540, d362613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44540, d362613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44541 q = 1) (hb : d362614 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44541, d362614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44541, d362614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro100030 (p : Pattern) (ha : d44547 p = 1) (hb : d362620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44542 q = 1) (hb : d362615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, d362615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100029 q ha hb
    | true =>
      simp only [d44542, d362615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44543 q = 1) (hb : d362616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, d362616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44543, d362616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44544 q = 1) (hb : d362617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, d362617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, d362617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44545 q = 1) (hb : d362618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, d362618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, d362618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44546 q = 1) (hb : d362619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, d362619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, d362619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44547 q = 1) (hb : d362620 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44547, d362620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44547, d362620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100031 (p : Pattern) (ha : d44609 p = 1) (hb : d362623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d362510 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d362510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d362510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99999 q ha hb
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d362511 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d362511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, d362511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99998 q ha hb
  have h3 (q : Pattern) (ha : d35373 q = 1) (hb : d362512 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d362512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d362512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44441 q = 1) (hb : d362513 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d362513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, d362513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44442 q = 1) (hb : d362514 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d362514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, d362514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44443 q = 1) (hb : d362515 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d362515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, d362515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44609 q = 1) (hb : d362623 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44609, d362623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44609, d362623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro100032 (p : Pattern) (ha : d44615 p = 1) (hb : d362629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d362519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d362519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d362520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d362520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d362535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d362535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d362536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d362536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d362537 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d362537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d362537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44610 q = 1) (hb : d362624 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100031 q ha hb
    | true =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44611 q = 1) (hb : d362625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44612 q = 1) (hb : d362626 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, d362626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44612, d362626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44613 q = 1) (hb : d362627 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, d362627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44613, d362627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44614 q = 1) (hb : d362628 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, d362628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44614, d362628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44615 q = 1) (hb : d362629 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44615, d362629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44615, d362629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100033 (p : Pattern) (ha : d44616 p = 1) (hb : d362630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44610 q = 1) (hb : d362624 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100031 q ha hb
    | true =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44611 q = 1) (hb : d362625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44612 q = 1) (hb : d362626 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, d362626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44612, d362626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44613 q = 1) (hb : d362627 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, d362627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44613, d362627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44614 q = 1) (hb : d362628 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, d362628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44614, d362628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44616 q = 1) (hb : d362630 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44616, d362630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44616, d362630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100034 (p : Pattern) (ha : d44622 p = 1) (hb : d362636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44468 q = 1) (hb : d362541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d362541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100004 q ha hb
    | true =>
      simp only [d44468, d362541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
  have h2 (q : Pattern) (ha : d44469 q = 1) (hb : d362542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d362542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d362542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44470 q = 1) (hb : d362543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d362543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d362543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44478 q = 1) (hb : d362551 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100005 q ha hb
    | true =>
      simp only [d44478, d362551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100007 q ha hb
  have h5 (q : Pattern) (ha : d44479 q = 1) (hb : d362552 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d362552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44480 q = 1) (hb : d362553 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d362553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44481 q = 1) (hb : d362554 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d362554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, d362554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44617 q = 1) (hb : d362631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44617, d362631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100032 q ha hb
    | true =>
      simp only [d44617, d362631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100033 q ha hb
  have h9 (q : Pattern) (ha : d44618 q = 1) (hb : d362632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44618, d362632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44618, d362632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44619 q = 1) (hb : d362633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44619, d362633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44619, d362633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44620 q = 1) (hb : d362634 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44620, d362634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44620, d362634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44621 q = 1) (hb : d362635 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44621, d362635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44621, d362635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44622 q = 1) (hb : d362636 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44622, d362636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44622, d362636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro100035 (p : Pattern) (ha : d44628 p = 1) (hb : d362642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44623 q = 1) (hb : d362637 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, d362637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100034 q ha hb
    | true =>
      simp only [d44623, d362637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44624 q = 1) (hb : d362638 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, d362638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44624, d362638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44625 q = 1) (hb : d362639 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, d362639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, d362639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44626 q = 1) (hb : d362640 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, d362640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, d362640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44627 q = 1) (hb : d362641 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, d362641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, d362641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44628 q = 1) (hb : d362642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44628, d362642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44628, d362642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100036 (p : Pattern) (ha : d309471 p = 1) (hb : d362648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44522 q = 1) (hb : d362595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, d362595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100024 q ha hb
    | true =>
      simp only [d44522, d362595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100025 q ha hb
  have h2 (q : Pattern) (ha : d44523 q = 1) (hb : d362596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, d362596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44523, d362596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44524 q = 1) (hb : d362597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, d362597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, d362597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44525 q = 1) (hb : d362598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, d362598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44525, d362598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44532 q = 1) (hb : d362605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, d362605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100026 q ha hb
    | true =>
      simp only [d44532, d362605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100027 q ha hb
  have h6 (q : Pattern) (ha : d44533 q = 1) (hb : d362606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, d362606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44533, d362606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44534 q = 1) (hb : d362607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, d362607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, d362607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44548 q = 1) (hb : d362621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, d362621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100030 q ha hb
    | true =>
      simp only [d44548, d362621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d309467 q = 1) (hb : d362622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309467, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44629 q = 1) (hb : d362643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, d362643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100035 q ha hb
    | true =>
      simp only [d44629, d362643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44630 q = 1) (hb : d362644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, d362644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44630, d362644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d309468 q = 1) (hb : d362645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309468, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309469 q = 1) (hb : d362646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309469, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309470 q = 1) (hb : d362647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309470, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309471 q = 1) (hb : d362648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309471, d362648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309471, d362648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100037 (p : Pattern) (ha : d44635 p = 1) (hb : d362649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d362564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d362565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d362565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44518 q = 1) (hb : d362591 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, d362591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44518, d362591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44635 q = 1) (hb : d362649 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44635, d362649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44635, d362649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100038 (p : Pattern) (ha : d44636 p = 1) (hb : d362650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d362568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d362569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d362569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44520 q = 1) (hb : d362593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, d362593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44520, d362593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44636 q = 1) (hb : d362650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44636, d362650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44636, d362650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100039 (p : Pattern) (ha : d44641 p = 1) (hb : d362655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d362564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d362564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44526 q = 1) (hb : d362599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, d362599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44526, d362599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44527 q = 1) (hb : d362600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, d362600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, d362600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44641 q = 1) (hb : d362655 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44641, d362655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44641, d362655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100040 (p : Pattern) (ha : d44642 p = 1) (hb : d362656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d362562 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100009 q ha hb
    | true =>
      simp only [d44489, d362562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d362563 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d362563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d362568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d362568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44529 q = 1) (hb : d362602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, d362602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44529, d362602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44530 q = 1) (hb : d362603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, d362603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, d362603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44642 q = 1) (hb : d362656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44642, d362656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44642, d362656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100041 (p : Pattern) (ha : d44646 p = 1) (hb : d362660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44542 q = 1) (hb : d362615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, d362615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100029 q ha hb
    | true =>
      simp only [d44542, d362615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44543 q = 1) (hb : d362616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, d362616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44543, d362616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44485 q = 1) (hb : d362558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100008 q ha hb
    | true =>
      simp only [d44485, d362558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44486 q = 1) (hb : d362559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d362559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44544 q = 1) (hb : d362617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, d362617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, d362617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44545 q = 1) (hb : d362618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, d362618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, d362618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44546 q = 1) (hb : d362619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, d362619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, d362619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44646 q = 1) (hb : d362660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44646, d362660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44646, d362660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100042 (p : Pattern) (ha : d44652 p = 1) (hb : d362663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44623 q = 1) (hb : d362637 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, d362637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100034 q ha hb
    | true =>
      simp only [d44623, d362637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44624 q = 1) (hb : d362638 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, d362638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44624, d362638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44625 q = 1) (hb : d362639 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, d362639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, d362639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44626 q = 1) (hb : d362640 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, d362640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, d362640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44627 q = 1) (hb : d362641 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, d362641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, d362641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44652 q = 1) (hb : d362663 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44652, d362663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44652, d362663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100043 (p : Pattern) (ha : d309476 p = 1) (hb : d362669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44522 q = 1) (hb : d362595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, d362595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100024 q ha hb
    | true =>
      simp only [d44522, d362595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100025 q ha hb
  have h2 (q : Pattern) (ha : d44523 q = 1) (hb : d362596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, d362596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44523, d362596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44524 q = 1) (hb : d362597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, d362597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, d362597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44525 q = 1) (hb : d362598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, d362598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44525, d362598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44532 q = 1) (hb : d362605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, d362605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100026 q ha hb
    | true =>
      simp only [d44532, d362605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100027 q ha hb
  have h6 (q : Pattern) (ha : d44533 q = 1) (hb : d362606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, d362606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44533, d362606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44534 q = 1) (hb : d362607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, d362607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, d362607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44548 q = 1) (hb : d362621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, d362621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100030 q ha hb
    | true =>
      simp only [d44548, d362621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d309467 q = 1) (hb : d362622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309467, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44629 q = 1) (hb : d362643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, d362643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100035 q ha hb
    | true =>
      simp only [d44629, d362643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44630 q = 1) (hb : d362644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, d362644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44630, d362644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d309468 q = 1) (hb : d362645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309468, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309469 q = 1) (hb : d362646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309469, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309470 q = 1) (hb : d362647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309470, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44637 q = 1) (hb : d362651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44637, d362651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100037 q ha hb
    | true =>
      simp only [d44637, d362651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100038 q ha hb
  have h17 (q : Pattern) (ha : d44638 q = 1) (hb : d362652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44638, d362652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44638, d362652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44639 q = 1) (hb : d362653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44639, d362653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d44639, d362653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d44640 q = 1) (hb : d362654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44640, d362654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44640, d362654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d44643 q = 1) (hb : d362657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44643, d362657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100039 q ha hb
    | true =>
      simp only [d44643, d362657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100040 q ha hb
  have h21 (q : Pattern) (ha : d44644 q = 1) (hb : d362658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44644, d362658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44644, d362658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d44645 q = 1) (hb : d362659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44645, d362659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d44645, d362659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d44647 q = 1) (hb : d362661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, d362661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100041 q ha hb
    | true =>
      simp only [d44647, d362661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100013 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d362582 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d309472 q = 1) (hb : d362662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309472, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d44653 q = 1) (hb : d362664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, d362664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100042 q ha hb
    | true =>
      simp only [d44653, d362664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d44654 q = 1) (hb : d362665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, d362665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d44654, d362665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d309473 q = 1) (hb : d362666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d309473, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d309474 q = 1) (hb : d362667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309474, d362667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309474, d362667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d309475 q = 1) (hb : d362668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309475, d362668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309475, d362668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d309476 q = 1) (hb : d362669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309476, d362669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309476, d362669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro100044 (p : Pattern) (ha : d309483 p = 1) (hb : d362689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44647 q = 1) (hb : d362661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, d362661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100041 q ha hb
    | true =>
      simp only [d44647, d362661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100013 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362582 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309472 q = 1) (hb : d362662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309472, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44653 q = 1) (hb : d362664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, d362664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100042 q ha hb
    | true =>
      simp only [d44653, d362664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44654 q = 1) (hb : d362665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, d362665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44654, d362665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309473 q = 1) (hb : d362666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309473, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309481 q = 1) (hb : d362687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309481, d362687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309481, d362687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309482 q = 1) (hb : d362688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309482, d362688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309482, d362688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309483 q = 1) (hb : d362689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309483, d362689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309483, d362689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100045 (p : Pattern) (ha : d44691 p = 1) (hb : d362702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d362697 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d362698 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d362699 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d362700 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44690 q = 1) (hb : d362701 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, d362701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44690, d362701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44691 q = 1) (hb : d362702 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44691, d362702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44691, d362702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100046 (p : Pattern) (ha : d44697 p = 1) (hb : d362708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d362697 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d362698 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d362699 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d362700 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44690 q = 1) (hb : d362701 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, d362701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44690, d362701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44692 q = 1) (hb : d362703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
  have h9 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44693 q = 1) (hb : d362704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44694 q = 1) (hb : d362705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44695 q = 1) (hb : d362706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44696 q = 1) (hb : d362707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d362707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d362707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d44697 q = 1) (hb : d362708 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44697, d362708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44697, d362708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100047 (p : Pattern) (ha : d44718 p = 1) (hb : d362729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44698 q = 1) (hb : d362709 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44698, d362709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100045 q ha hb
    | true =>
      simp only [d44698, d362709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100046 q ha hb
  have h2 (q : Pattern) (ha : d44699 q = 1) (hb : d362710 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44699, d362710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44699, d362710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44700 q = 1) (hb : d362711 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44700, d362711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44700, d362711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44703 q = 1) (hb : d362714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d362714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100046 q ha hb
    | true =>
      simp only [d44703, d362714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
  have h5 (q : Pattern) (ha : d44704 q = 1) (hb : d362715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d362715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d362715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44705 q = 1) (hb : d362716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d362716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d362716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44706 q = 1) (hb : d362717 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44706, d362717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44706, d362717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44713 q = 1) (hb : d362724 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
    | true =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100020 q ha hb
  have h9 (q : Pattern) (ha : d44714 q = 1) (hb : d362725 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44715 q = 1) (hb : d362726 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44716 q = 1) (hb : d362727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d362727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44716, d362727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44717 q = 1) (hb : d362728 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44717, d362728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44717, d362728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44718 q = 1) (hb : d362729 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44718, d362729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44718, d362729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro100048 (p : Pattern) (ha : d44723 p = 1) (hb : d362734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d362714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d362714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100046 q ha hb
    | true =>
      simp only [d44703, d362714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d362715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d362715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d362715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d362716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d362716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d362716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d362724 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
    | true =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100020 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d362725 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d362726 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d362727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d362727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d362727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44721 q = 1) (hb : d362732 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d362732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44721, d362732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44722 q = 1) (hb : d362733 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44722, d362733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44722, d362733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44723 q = 1) (hb : d362734 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44723, d362734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44723, d362734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro100049 (p : Pattern) (ha : d44729 p = 1) (hb : d362740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44719 q = 1) (hb : d362730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44719, d362730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100047 q ha hb
    | true =>
      simp only [d44719, d362730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44720 q = 1) (hb : d362731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44720, d362731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44720, d362731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44724 q = 1) (hb : d362735 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d362735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100048 q ha hb
    | true =>
      simp only [d44724, d362735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44725 q = 1) (hb : d362736 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d362736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d362736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44726 q = 1) (hb : d362737 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44726, d362737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44726, d362737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44727 q = 1) (hb : d362738 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44727, d362738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44727, d362738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44728 q = 1) (hb : d362739 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44728, d362739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44728, d362739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44729 q = 1) (hb : d362740 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44729, d362740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44729, d362740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100050 (p : Pattern) (ha : d44737 p = 1) (hb : d362748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44724 q = 1) (hb : d362735 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d362735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100048 q ha hb
    | true =>
      simp only [d44724, d362735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44725 q = 1) (hb : d362736 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d362736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d362736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44732 q = 1) (hb : d362743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d362743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100021 q ha hb
    | true =>
      simp only [d44732, d362743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44733 q = 1) (hb : d362744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d362744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d362744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44734 q = 1) (hb : d362745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44734, d362745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44734, d362745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44735 q = 1) (hb : d362746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44735, d362746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44735, d362746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44736 q = 1) (hb : d362747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44736, d362747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44736, d362747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44737 q = 1) (hb : d362748 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44737, d362748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44737, d362748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100051 (p : Pattern) (ha : d44789 p = 1) (hb : d362761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d362697 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d362697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d362517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100000 q ha hb
    | true =>
      simp only [d44445, d362517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d362698 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d362698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d362518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d362518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d362699 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d362699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d362700 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d362700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d362703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d362703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d362533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100003 q ha hb
    | true =>
      simp only [d44460, d362533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d362704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d362704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d362534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d362534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d362705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d362705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d362706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d362706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d362707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d362707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d362707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44784 q = 1) (hb : d362756 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, d362756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44784, d362756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100031 q ha hb
  have h15 (q : Pattern) (ha : d44610 q = 1) (hb : d362624 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100031 q ha hb
    | true =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44785 q = 1) (hb : d362757 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, d362757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44785, d362757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44611 q = 1) (hb : d362625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d44786 q = 1) (hb : d362758 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, d362758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44786, d362758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44787 q = 1) (hb : d362759 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, d362759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44787, d362759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d44788 q = 1) (hb : d362760 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, d362760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44788, d362760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d44789 q = 1) (hb : d362761 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44789, d362761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44789, d362761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100052 (p : Pattern) (ha : d44790 p = 1) (hb : d362762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44784 q = 1) (hb : d362756 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, d362756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44784, d362756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100031 q ha hb
  have h2 (q : Pattern) (ha : d44610 q = 1) (hb : d362624 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100031 q ha hb
    | true =>
      simp only [d44610, d362624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44785 q = 1) (hb : d362757 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, d362757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44785, d362757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44611 q = 1) (hb : d362625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44611, d362625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44786 q = 1) (hb : d362758 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, d362758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44786, d362758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44787 q = 1) (hb : d362759 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, d362759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44787, d362759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44788 q = 1) (hb : d362760 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, d362760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44788, d362760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44790 q = 1) (hb : d362762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44790, d362762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44790, d362762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100053 (p : Pattern) (ha : d44796 p = 1) (hb : d362768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d362714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d362714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100046 q ha hb
    | true =>
      simp only [d44703, d362714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d362715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d362715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d362715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d362716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d362716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d362716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d362724 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100019 q ha hb
    | true =>
      simp only [d44713, d362724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100020 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d362725 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d362725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d362726 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d362726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d362727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d362727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d362727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44791 q = 1) (hb : d362763 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44791, d362763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100051 q ha hb
    | true =>
      simp only [d44791, d362763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100052 q ha hb
  have h9 (q : Pattern) (ha : d44792 q = 1) (hb : d362764 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44792, d362764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44792, d362764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44793 q = 1) (hb : d362765 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44793, d362765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44793, d362765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44794 q = 1) (hb : d362766 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44794, d362766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44794, d362766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44795 q = 1) (hb : d362767 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44795, d362767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44795, d362767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44796 q = 1) (hb : d362768 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44796, d362768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44796, d362768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro100054 (p : Pattern) (ha : d44802 p = 1) (hb : d362774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44797 q = 1) (hb : d362769 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44797, d362769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100053 q ha hb
    | true =>
      simp only [d44797, d362769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44798 q = 1) (hb : d362770 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44798, d362770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44798, d362770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44799 q = 1) (hb : d362771 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44799, d362771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44799, d362771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44800 q = 1) (hb : d362772 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44800, d362772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44800, d362772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44801 q = 1) (hb : d362773 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44801, d362773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44801, d362773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44802 q = 1) (hb : d362774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44802, d362774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44802, d362774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100055 (p : Pattern) (ha : d309493 p = 1) (hb : d362780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44738 q = 1) (hb : d362749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44738, d362749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100049 q ha hb
    | true =>
      simp only [d44738, d362749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100050 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309489 q = 1) (hb : d362755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309489, d362755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309489, d362755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44803 q = 1) (hb : d362775 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44803, d362775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100054 q ha hb
    | true =>
      simp only [d44803, d362775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44804 q = 1) (hb : d362776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44804, d362776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44804, d362776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309490 q = 1) (hb : d362777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309490, d362777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309490, d362777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309491 q = 1) (hb : d362778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309491, d362778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309491, d362778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309492 q = 1) (hb : d362779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309492, d362779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309492, d362779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309493 q = 1) (hb : d362780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309493, d362780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309493, d362780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100056 (p : Pattern) (ha : d309499 p = 1) (hb : d362793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44505 q = 1) (hb : d362578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44505, d362578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44505, d362578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100012 q ha hb
  have h2 (q : Pattern) (ha : d44506 q = 1) (hb : d362579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44506, d362579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44506, d362579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44515 q = 1) (hb : d362588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d362588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100012 q ha hb
    | true =>
      simp only [d44515, d362588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100015 q ha hb
  have h4 (q : Pattern) (ha : d44516 q = 1) (hb : d362589 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d362589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44516, d362589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44517 q = 1) (hb : d362590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44517, d362590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44517, d362590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309477 q = 1) (hb : d362670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309477, d362670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100036 q ha hb
    | true =>
      simp only [d309477, d362670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100043 q ha hb
  have h7 (q : Pattern) (ha : d44672 q = 1) (hb : d362683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44672, d362683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100016 q ha hb
    | true =>
      simp only [d44672, d362683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100017 q ha hb
  have h8 (q : Pattern) (ha : d309478 q = 1) (hb : d362684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309478, d362684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309478, d362684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309479 q = 1) (hb : d362685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309479, d362685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309479, d362685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d309480 q = 1) (hb : d362686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309480, d362686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309480, d362686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309484 q = 1) (hb : d362690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309484, d362690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309484, d362690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100044 q ha hb
  have h12 (q : Pattern) (ha : d44681 q = 1) (hb : d362692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44681, d362692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44681, d362692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100018 q ha hb
  have h13 (q : Pattern) (ha : d309485 q = 1) (hb : d362693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309485, d362693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309485, d362693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309486 q = 1) (hb : d362694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309486, d362694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309486, d362694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d309487 q = 1) (hb : d362695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309487, d362695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309487, d362695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d309488 q = 1) (hb : d362696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309488, d362696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309488, d362696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309494 q = 1) (hb : d362781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309494, d362781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309494, d362781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100055 q ha hb
  have h18 (q : Pattern) (ha : d44820 q = 1) (hb : d362788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44820, d362788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44820, d362788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100023 q ha hb
  have h19 (q : Pattern) (ha : d309495 q = 1) (hb : d362789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309495, d362789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309495, d362789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d309496 q = 1) (hb : d362790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309496, d362790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309496, d362790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d309497 q = 1) (hb : d362791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309497, d362791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309497, d362791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d309498 q = 1) (hb : d362792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309498, d362792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309498, d362792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d309499 q = 1) (hb : d362793 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309499, d362793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309499, d362793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100057 (p : Pattern) (ha : d309505 p = 1) (hb : d362799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309500 q = 1) (hb : d362794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309500, d362794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309500, d362794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100056 q ha hb
  have h2 (q : Pattern) (ha : d309501 q = 1) (hb : d362795 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309501, d362795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309501, d362795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309502 q = 1) (hb : d362796 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309502, d362796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309502, d362796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309503 q = 1) (hb : d362797 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309503, d362797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309503, d362797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309504 q = 1) (hb : d362798 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309504, d362798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309504, d362798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309505 q = 1) (hb : d362799 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309505, d362799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309505, d362799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100058 (p : Pattern) (ha : d362804 p = 1) (hb : d362848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362803 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309506 q = 1) (hb : d362800 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309506, d362800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309506, d362800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100057 q ha hb
  have h4 (q : Pattern) (ha : d309507 q = 1) (hb : d362801 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309507, d362801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309507, d362801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309508 q = 1) (hb : d362802 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309508, d362802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309508, d362802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309509 q = 1) (hb : d362803 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309509, d362803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309509, d362803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362803 q = 1) (hb : d362847 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d362847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d362804 q = 1) (hb : d362848 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d362804, d362848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362804, d362848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro100059 (p : Pattern) (ha : d362810 p = 1) (hb : d362854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362805 q = 1) (hb : d362849 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d362805, d362849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100058 q ha hb
    | true =>
      simp only [d362805, d362849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362806 q = 1) (hb : d362850 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d362806, d362850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362806, d362850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362807 q = 1) (hb : d362851 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d362807, d362851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362807, d362851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362808 q = 1) (hb : d362852 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d362808, d362852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362808, d362852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362809 q = 1) (hb : d362853 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d362809, d362853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362809, d362853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362810 q = 1) (hb : d362854 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d362810, d362854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362810, d362854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100060 (p : Pattern) (ha : d362816 p = 1) (hb : d362860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362811 q = 1) (hb : d362855 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d362811, d362855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100059 q ha hb
    | true =>
      simp only [d362811, d362855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362812 q = 1) (hb : d362856 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d362812, d362856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362812, d362856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362813 q = 1) (hb : d362857 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d362813, d362857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362813, d362857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362814 q = 1) (hb : d362858 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d362814, d362858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362814, d362858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362815 q = 1) (hb : d362859 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d362815, d362859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362815, d362859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362816 q = 1) (hb : d362860 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d362816, d362860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362816, d362860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100061 (p : Pattern) (ha : d362822 p = 1) (hb : d362866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362817 q = 1) (hb : d362861 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d362817, d362861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100060 q ha hb
    | true =>
      simp only [d362817, d362861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362818 q = 1) (hb : d362862 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d362818, d362862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362818, d362862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362819 q = 1) (hb : d362863 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d362819, d362863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362819, d362863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362820 q = 1) (hb : d362864 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d362820, d362864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362820, d362864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362821 q = 1) (hb : d362865 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d362821, d362865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362821, d362865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362822 q = 1) (hb : d362866 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d362822, d362866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362822, d362866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100062 (p : Pattern) (ha : d362828 p = 1) (hb : d362872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362823 q = 1) (hb : d362867 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d362823, d362867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100061 q ha hb
    | true =>
      simp only [d362823, d362867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362824 q = 1) (hb : d362868 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d362824, d362868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362824, d362868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362825 q = 1) (hb : d362869 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d362825, d362869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362825, d362869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362826 q = 1) (hb : d362870 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d362826, d362870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362826, d362870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362827 q = 1) (hb : d362871 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d362827, d362871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362827, d362871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362828 q = 1) (hb : d362872 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d362828, d362872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362828, d362872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100063 (p : Pattern) (ha : d362834 p = 1) (hb : d362878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362829 q = 1) (hb : d362873 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d362829, d362873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100062 q ha hb
    | true =>
      simp only [d362829, d362873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362830 q = 1) (hb : d362874 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d362830, d362874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362830, d362874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362831 q = 1) (hb : d362875 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d362831, d362875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362831, d362875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362832 q = 1) (hb : d362876 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d362832, d362876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362832, d362876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362833 q = 1) (hb : d362877 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d362833, d362877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362833, d362877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362834 q = 1) (hb : d362878 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d362834, d362878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362834, d362878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100064 (p : Pattern) (ha : d362840 p = 1) (hb : d362884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362835 q = 1) (hb : d362879 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d362835, d362879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100063 q ha hb
    | true =>
      simp only [d362835, d362879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362836 q = 1) (hb : d362880 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d362836, d362880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362836, d362880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362837 q = 1) (hb : d362881 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d362837, d362881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362837, d362881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362838 q = 1) (hb : d362882 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d362838, d362882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362838, d362882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362839 q = 1) (hb : d362883 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d362839, d362883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362839, d362883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362840 q = 1) (hb : d362884 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d362840, d362884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362840, d362884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100065 (p : Pattern) (ha : d362846 p = 1) (hb : d362890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362841 q = 1) (hb : d362885 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d362841, d362885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100064 q ha hb
    | true =>
      simp only [d362841, d362885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362842 q = 1) (hb : d362886 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d362842, d362886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362842, d362886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362843 q = 1) (hb : d362887 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d362843, d362887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362843, d362887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362844 q = 1) (hb : d362888 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d362844, d362888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362844, d362888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362845 q = 1) (hb : d362889 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d362845, d362889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362845, d362889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362846 q = 1) (hb : d362890 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d362846, d362890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362846, d362890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100066 (p : Pattern) (ha : d357556 p = 1) (hb : d358935 p = 1) : d362892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357554 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d309722 q = 1) : d309722 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d357555 q = 1) (hb : d358935 q = 1) : d362891 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d358935, d362891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357555, d358935, d362891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d358935 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357556 q = 1) (hb : d358935 q = 1) : d362892 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d362892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357556, d362892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro100067 (p : Pattern) (ha : d357562 p = 1) (hb : d358935 p = 1) : d362898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d358935 q = 1) : d362893 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d362893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100066 q ha hb
    | true =>
      simp only [d357557, d362893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d358935 q = 1) : d362894 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d362894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d362894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d358935 q = 1) : d362895 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d362895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d362895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d358935 q = 1) : d362896 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d362896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d362896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d358935 q = 1) : d362897 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d362897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d362897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357562 q = 1) (hb : d358935 q = 1) : d362898 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d362898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d362898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100068 (p : Pattern) (ha : d357568 p = 1) (hb : d358937 p = 1) : d362904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d358935 q = 1) : d362899 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d362899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100067 q ha hb
    | true =>
      simp only [d357563, d362899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d358935 q = 1) : d362900 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d362900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d362900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d358935 q = 1) : d362901 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d362901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d362901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357566 q = 1) (hb : d358936 q = 1) : d362902 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d358936, d362902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d358936, d362902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d357567 q = 1) (hb : d358937 q = 1) : d362903 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d358937, d362903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357567, d358937, d362903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d358937 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d357568 q = 1) (hb : d358937 q = 1) : d362904 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d362904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357568, d362904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100069 (p : Pattern) (ha : d357574 p = 1) (hb : d358937 p = 1) : d362910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d358937 q = 1) : d362905 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d362905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100068 q ha hb
    | true =>
      simp only [d357569, d362905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d358937 q = 1) : d362906 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d362906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d362906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d358937 q = 1) : d362907 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d362907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d362907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d358937 q = 1) : d362908 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d362908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d362908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d358937 q = 1) : d362909 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d362909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d362909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d358937 q = 1) : d362910 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d362910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d362910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100070 (p : Pattern) (ha : d357580 p = 1) (hb : d358937 p = 1) : d362916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d358937 q = 1) : d362911 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d362911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100069 q ha hb
    | true =>
      simp only [d357575, d362911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d358937 q = 1) : d362912 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d362912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d362912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d358937 q = 1) : d362913 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d362913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d362913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d358937 q = 1) : d362914 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d362914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d362914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d358937 q = 1) : d362915 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d362915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d362915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d358937 q = 1) : d362916 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d362916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d362916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100071 (p : Pattern) (ha : d357586 p = 1) (hb : d358937 p = 1) : d362922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d358937 q = 1) : d362917 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d362917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100070 q ha hb
    | true =>
      simp only [d357581, d362917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d358937 q = 1) : d362918 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d362918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d362918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d358937 q = 1) : d362919 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d362919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d362919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d358937 q = 1) : d362920 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d362920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d362920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d358937 q = 1) : d362921 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d362921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d362921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d358937 q = 1) : d362922 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d362922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d362922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100072 (p : Pattern) (ha : d357592 p = 1) (hb : d358937 p = 1) : d362928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d358937 q = 1) : d362923 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d362923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100071 q ha hb
    | true =>
      simp only [d357587, d362923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d358937 q = 1) : d362924 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d362924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d362924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d358937 q = 1) : d362925 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d362925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d362925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d358937 q = 1) : d362926 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d362926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d362926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d358937 q = 1) : d362927 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d362927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d362927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d358937 q = 1) : d362928 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d362928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d362928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100073 (p : Pattern) (ha : d357598 p = 1) (hb : d358937 p = 1) : d362934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d358937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d358937 q = 1) : d362929 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d362929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100072 q ha hb
    | true =>
      simp only [d357593, d362929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d358937 q = 1) : d362930 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d362930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d362930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d358937 q = 1) : d362931 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d362931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d362931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d358937 q = 1) : d362932 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d362932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d362932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d358937 q = 1) : d362933 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d362933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d362933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d358937 q = 1) : d362934 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d362934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d362934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100074 (p : Pattern) (ha : d44504 p = 1) (hb : d362648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362607 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d362621 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44499 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
    | true =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d362622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d362644 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d362645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d362646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d362647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d362648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d362648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d362648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100075 (p : Pattern) (ha : d44514 p = 1) (hb : d362669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362607 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44499 q = 1) (hb : d362572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100010 q ha hb
    | true =>
      simp only [d44499, d362572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100011 q ha hb
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d362622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d362622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d362644 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d362645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d362645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d362646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d362646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d362647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d362647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d362654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d362659 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d362661 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44509 q = 1) (hb : d362582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d362582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100013 q ha hb
    | true =>
      simp only [d44509, d362582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100014 q ha hb
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d362662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d362665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d362666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d362667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d362667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d362667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d362668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d362668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d362668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d362669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d362669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d362669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100076 (p : Pattern) (ha : d309695 p = 1) (hb : d362689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44509 q = 1) (hb : d362582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d362582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100013 q ha hb
    | true =>
      simp only [d44509, d362582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100014 q ha hb
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d362662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d362662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d362665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d362666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d362666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d362687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d362687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d362687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d362688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d362688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d362688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309695 q = 1) (hb : d362689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309695, d362689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309695, d362689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100077 (p : Pattern) (ha : d309706 p = 1) (hb : d362780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362749 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309701 q = 1) (hb : d362754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d309701, d362754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100050 q ha hb
    | true =>
      simp only [d309701, d362754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100022 q ha hb
  have h3 (q : Pattern) (ha : d309702 q = 1) (hb : d362755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309702, d362755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309702, d362755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d362776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309703 q = 1) (hb : d362777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309703, d362777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309703, d362777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309704 q = 1) (hb : d362778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309704, d362778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309704, d362778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309705 q = 1) (hb : d362779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309705, d362779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309705, d362779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309706 q = 1) (hb : d362780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309706, d362780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309706, d362780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100078 (p : Pattern) (ha : d309712 p = 1) (hb : d362793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d362670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d362670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100074 q ha hb
    | true =>
      simp only [d44515, d362670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100075 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d362684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d362684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d362684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309693 q = 1) (hb : d362685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309693, d362685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309693, d362685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309694 q = 1) (hb : d362686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309694, d362686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309694, d362686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309696 q = 1) (hb : d362690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309696, d362690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309696, d362690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100076 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d362692 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309697 q = 1) (hb : d362693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309697, d362693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309697, d362693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309698 q = 1) (hb : d362694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309698, d362694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309698, d362694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309699 q = 1) (hb : d362695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309699, d362695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309699, d362695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309700 q = 1) (hb : d362696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309700, d362696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309700, d362696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309707 q = 1) (hb : d362781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309707, d362781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309707, d362781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100077 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d362788 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309708 q = 1) (hb : d362789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309708, d362789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309708, d362789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309709 q = 1) (hb : d362790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309709, d362790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309709, d362790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309710 q = 1) (hb : d362791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309710, d362791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309710, d362791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309711 q = 1) (hb : d362792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309711, d362792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309711, d362792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309712 q = 1) (hb : d362793 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309712, d362793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309712, d362793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100079 (p : Pattern) (ha : d309718 p = 1) (hb : d362799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309713 q = 1) (hb : d362794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309713, d362794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309713, d362794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100078 q ha hb
  have h2 (q : Pattern) (ha : d309714 q = 1) (hb : d362795 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309714, d362795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309714, d362795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309715 q = 1) (hb : d362796 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309715, d362796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309715, d362796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309716 q = 1) (hb : d362797 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309716, d362797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309716, d362797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309717 q = 1) (hb : d362798 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309717, d362798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309717, d362798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309718 q = 1) (hb : d362799 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309718, d362799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309718, d362799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100080 (p : Pattern) (ha : d362804 p = 1) (hb : d362892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362803 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309719 q = 1) (hb : d362800 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309719, d362800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309719, d362800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100079 q ha hb
  have h4 (q : Pattern) (ha : d309720 q = 1) (hb : d362801 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309720, d362801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309720, d362801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309721 q = 1) (hb : d362802 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309721, d362802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309721, d362802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309722 q = 1) (hb : d362803 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309722, d362803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309722, d362803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362803 q = 1) (hb : d362891 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d362891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d362804 q = 1) (hb : d362892 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d362804, d362892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362804, d362892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro100081 (p : Pattern) (ha : d362810 p = 1) (hb : d362898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362805 q = 1) (hb : d362893 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d362805, d362893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100080 q ha hb
    | true =>
      simp only [d362805, d362893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362806 q = 1) (hb : d362894 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d362806, d362894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362806, d362894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362807 q = 1) (hb : d362895 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d362807, d362895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362807, d362895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362808 q = 1) (hb : d362896 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d362808, d362896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362808, d362896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362809 q = 1) (hb : d362897 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d362809, d362897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362809, d362897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362810 q = 1) (hb : d362898 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d362810, d362898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362810, d362898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100082 (p : Pattern) (ha : d362816 p = 1) (hb : d362904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362811 q = 1) (hb : d362899 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d362811, d362899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100081 q ha hb
    | true =>
      simp only [d362811, d362899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362812 q = 1) (hb : d362900 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d362812, d362900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362812, d362900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362813 q = 1) (hb : d362901 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d362813, d362901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362813, d362901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362814 q = 1) (hb : d362902 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d362814, d362902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362814, d362902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362815 q = 1) (hb : d362903 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d362815, d362903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362815, d362903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362816 q = 1) (hb : d362904 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d362816, d362904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362816, d362904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100083 (p : Pattern) (ha : d362822 p = 1) (hb : d362910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362817 q = 1) (hb : d362905 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d362817, d362905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100082 q ha hb
    | true =>
      simp only [d362817, d362905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362818 q = 1) (hb : d362906 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d362818, d362906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362818, d362906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362819 q = 1) (hb : d362907 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d362819, d362907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362819, d362907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362820 q = 1) (hb : d362908 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d362820, d362908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362820, d362908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362821 q = 1) (hb : d362909 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d362821, d362909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362821, d362909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362822 q = 1) (hb : d362910 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d362822, d362910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362822, d362910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100084 (p : Pattern) (ha : d362828 p = 1) (hb : d362916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362823 q = 1) (hb : d362911 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d362823, d362911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100083 q ha hb
    | true =>
      simp only [d362823, d362911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362824 q = 1) (hb : d362912 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d362824, d362912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362824, d362912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362825 q = 1) (hb : d362913 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d362825, d362913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362825, d362913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362826 q = 1) (hb : d362914 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d362826, d362914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362826, d362914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362827 q = 1) (hb : d362915 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d362827, d362915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362827, d362915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362828 q = 1) (hb : d362916 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d362828, d362916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362828, d362916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100085 (p : Pattern) (ha : d362834 p = 1) (hb : d362922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362829 q = 1) (hb : d362917 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d362829, d362917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100084 q ha hb
    | true =>
      simp only [d362829, d362917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362830 q = 1) (hb : d362918 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d362830, d362918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362830, d362918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362831 q = 1) (hb : d362919 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d362831, d362919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362831, d362919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362832 q = 1) (hb : d362920 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d362832, d362920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362832, d362920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362833 q = 1) (hb : d362921 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d362833, d362921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362833, d362921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362834 q = 1) (hb : d362922 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d362834, d362922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362834, d362922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100086 (p : Pattern) (ha : d362840 p = 1) (hb : d362928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362835 q = 1) (hb : d362923 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d362835, d362923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100085 q ha hb
    | true =>
      simp only [d362835, d362923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362836 q = 1) (hb : d362924 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d362836, d362924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362836, d362924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362837 q = 1) (hb : d362925 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d362837, d362925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362837, d362925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362838 q = 1) (hb : d362926 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d362838, d362926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362838, d362926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362839 q = 1) (hb : d362927 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d362839, d362927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362839, d362927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362840 q = 1) (hb : d362928 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d362840, d362928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362840, d362928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100087 (p : Pattern) (ha : d362846 p = 1) (hb : d362934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362841 q = 1) (hb : d362929 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d362841, d362929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100086 q ha hb
    | true =>
      simp only [d362841, d362929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362842 q = 1) (hb : d362930 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d362842, d362930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362842, d362930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362843 q = 1) (hb : d362931 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d362843, d362931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362843, d362931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362844 q = 1) (hb : d362932 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d362844, d362932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362844, d362932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362845 q = 1) (hb : d362933 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d362845, d362933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362845, d362933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362846 q = 1) (hb : d362934 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d362846, d362934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362846, d362934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100088 (p : Pattern) (ha : d44504 p = 1) (hb : d363139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360831 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d360840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d360854 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d363135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d363135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d363135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d360942 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d363136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d363136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d363136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d363137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d363137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d363137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d363138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d363138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d363138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d363139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d363139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d363139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100089 (p : Pattern) (ha : d44514 p = 1) (hb : d363144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d360831 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d360854 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d363135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d363135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d363135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d360942 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d363136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d363136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d363136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d363137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d363137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d363137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d363138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d363138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d363138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d360952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d360957 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d360959 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d363140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d363140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d363140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d360966 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d363141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d363141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d363141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d363142 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d363142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d363142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d363143 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d363143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d363143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d363144 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d363144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d363144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100090 (p : Pattern) (ha : d309695 p = 1) (hb : d363151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d363140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d363140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d363140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d360966 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d363141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d363141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d363141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d363149 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d363149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d363149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d363150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d363150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d363150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309695 q = 1) (hb : d363151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309695, d363151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309695, d363151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100091 (p : Pattern) (ha : d309706 p = 1) (hb : d363161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361050 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309702 q = 1) (hb : d363157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309702, d363157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309702, d363157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361116 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309703 q = 1) (hb : d363158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309703, d363158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309703, d363158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309704 q = 1) (hb : d363159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309704, d363159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309704, d363159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309705 q = 1) (hb : d363160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309705, d363160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309705, d363160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309706 q = 1) (hb : d363161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309706, d363161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309706, d363161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100092 (p : Pattern) (ha : d309712 p = 1) (hb : d363167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d360823 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d363145 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d363145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100088 q ha hb
    | true =>
      simp only [d44515, d363145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100089 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d360984 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d363146 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d363146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d363146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309693 q = 1) (hb : d363147 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309693, d363147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309693, d363147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309694 q = 1) (hb : d363148 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309694, d363148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309694, d363148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309696 q = 1) (hb : d363152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309696, d363152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309696, d363152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100090 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d360993 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309697 q = 1) (hb : d363153 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309697, d363153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309697, d363153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309698 q = 1) (hb : d363154 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309698, d363154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309698, d363154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309699 q = 1) (hb : d363155 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309699, d363155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309699, d363155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309700 q = 1) (hb : d363156 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309700, d363156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309700, d363156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309707 q = 1) (hb : d363162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309707, d363162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309707, d363162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100091 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d361132 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309708 q = 1) (hb : d363163 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309708, d363163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309708, d363163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309709 q = 1) (hb : d363164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309709, d363164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309709, d363164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309710 q = 1) (hb : d363165 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309710, d363165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309710, d363165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309711 q = 1) (hb : d363166 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309711, d363166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309711, d363166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309712 q = 1) (hb : d363167 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309712, d363167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309712, d363167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100093 (p : Pattern) (ha : d309718 p = 1) (hb : d363173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309713 q = 1) (hb : d363168 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309713, d363168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309713, d363168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100092 q ha hb
  have h2 (q : Pattern) (ha : d309714 q = 1) (hb : d363169 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309714, d363169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309714, d363169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309715 q = 1) (hb : d363170 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309715, d363170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309715, d363170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309716 q = 1) (hb : d363171 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309716, d363171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309716, d363171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309717 q = 1) (hb : d363172 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309717, d363172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309717, d363172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309718 q = 1) (hb : d363173 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309718, d363173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309718, d363173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100094 (p : Pattern) (ha : d362892 p = 1) (hb : d363178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363177 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d363134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309719 q = 1) (hb : d363174 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309719, d363174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309719, d363174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100093 q ha hb
  have h4 (q : Pattern) (ha : d309720 q = 1) (hb : d363175 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309720, d363175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309720, d363175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309721 q = 1) (hb : d363176 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309721, d363176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309721, d363176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309722 q = 1) (hb : d363177 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309722, d363177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309722, d363177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362891 q = 1) (hb : d363177 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d362891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362892 q = 1) (hb : d363178 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d362892, d363178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362892, d363178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h8 p ha hb
theorem andIntro100095 (p : Pattern) (ha : d362898 p = 1) (hb : d363184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362893 q = 1) (hb : d363179 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d362893, d363179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100094 q ha hb
    | true =>
      simp only [d362893, d363179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362894 q = 1) (hb : d363180 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d362894, d363180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362894, d363180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362895 q = 1) (hb : d363181 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d362895, d363181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362895, d363181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362896 q = 1) (hb : d363182 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d362896, d363182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362896, d363182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362897 q = 1) (hb : d363183 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d362897, d363183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362897, d363183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362898 q = 1) (hb : d363184 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d362898, d363184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362898, d363184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100096 (p : Pattern) (ha : d362904 p = 1) (hb : d363190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362899 q = 1) (hb : d363185 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d362899, d363185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100095 q ha hb
    | true =>
      simp only [d362899, d363185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362900 q = 1) (hb : d363186 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d362900, d363186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362900, d363186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362901 q = 1) (hb : d363187 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d362901, d363187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362901, d363187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362902 q = 1) (hb : d363188 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d362902, d363188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362902, d363188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362903 q = 1) (hb : d363189 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d362903, d363189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362903, d363189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362904 q = 1) (hb : d363190 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d362904, d363190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362904, d363190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100097 (p : Pattern) (ha : d362910 p = 1) (hb : d363196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362905 q = 1) (hb : d363191 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d362905, d363191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100096 q ha hb
    | true =>
      simp only [d362905, d363191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362906 q = 1) (hb : d363192 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d362906, d363192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362906, d363192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362907 q = 1) (hb : d363193 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d362907, d363193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362907, d363193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362908 q = 1) (hb : d363194 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d362908, d363194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362908, d363194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362909 q = 1) (hb : d363195 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d362909, d363195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362909, d363195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362910 q = 1) (hb : d363196 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d362910, d363196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362910, d363196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100098 (p : Pattern) (ha : d362916 p = 1) (hb : d363202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362911 q = 1) (hb : d363197 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d362911, d363197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100097 q ha hb
    | true =>
      simp only [d362911, d363197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362912 q = 1) (hb : d363198 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d362912, d363198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362912, d363198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362913 q = 1) (hb : d363199 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d362913, d363199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362913, d363199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362914 q = 1) (hb : d363200 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d362914, d363200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362914, d363200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362915 q = 1) (hb : d363201 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d362915, d363201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362915, d363201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362916 q = 1) (hb : d363202 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d362916, d363202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362916, d363202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100099 (p : Pattern) (ha : d362922 p = 1) (hb : d363208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362917 q = 1) (hb : d363203 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d362917, d363203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100098 q ha hb
    | true =>
      simp only [d362917, d363203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362918 q = 1) (hb : d363204 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d362918, d363204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362918, d363204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362919 q = 1) (hb : d363205 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d362919, d363205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362919, d363205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362920 q = 1) (hb : d363206 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d362920, d363206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362920, d363206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362921 q = 1) (hb : d363207 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d362921, d363207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362921, d363207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362922 q = 1) (hb : d363208 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d362922, d363208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362922, d363208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100100 (p : Pattern) (ha : d362928 p = 1) (hb : d363214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362923 q = 1) (hb : d363209 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d362923, d363209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100099 q ha hb
    | true =>
      simp only [d362923, d363209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362924 q = 1) (hb : d363210 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d362924, d363210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362924, d363210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362925 q = 1) (hb : d363211 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d362925, d363211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362925, d363211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362926 q = 1) (hb : d363212 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d362926, d363212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362926, d363212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362927 q = 1) (hb : d363213 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d362927, d363213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362927, d363213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362928 q = 1) (hb : d363214 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d362928, d363214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362928, d363214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100101 (p : Pattern) (ha : d362934 p = 1) (hb : d363220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362929 q = 1) (hb : d363215 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d362929, d363215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100100 q ha hb
    | true =>
      simp only [d362929, d363215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d362930 q = 1) (hb : d363216 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d362930, d363216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362930, d363216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d362931 q = 1) (hb : d363217 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d362931, d363217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362931, d363217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d362932 q = 1) (hb : d363218 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d362932, d363218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362932, d363218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362933 q = 1) (hb : d363219 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d362933, d363219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362933, d363219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d362934 q = 1) (hb : d363220 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d362934, d363220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362934, d363220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100102 (p : Pattern) (ha : d308 p = 1) (hb : d9771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d1085 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1086 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100103 (p : Pattern) (ha : d308 p = 1) (hb : d32153 p = 1) : d10054 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d1523 q = 1) : d1523 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1524 q = 1) : d2005 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1524, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1524, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1525 q = 1) : d2006 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1525, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1525, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d32153 q = 1) : d10054 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32153, d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32153, d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro100104 (p : Pattern) (ha : d308 p = 1) (hb : d43880 p = 1) : d363327 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43872 q = 1) : d43872 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43874 q = 1) : d43874 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43875 q = 1) : d44016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43875, d44016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43875, d44016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100103 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43876 q = 1) : d44017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43876, d44017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43876, d44017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43858 q = 1) : d43858 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43877 q = 1) : d363324 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43877, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43877, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43878 q = 1) : d363325 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43878, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43878, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43879 q = 1) : d363326 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43879, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43879, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43880 q = 1) : d363327 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43880, d363327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43880, d363327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100105 (p : Pattern) (ha : d308 p = 1) (hb : d43891 p = 1) : d363333 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43890 q = 1) : d43890 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43874 q = 1) : d43874 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43875 q = 1) : d44016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43875, d44016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43875, d44016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100103 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43876 q = 1) : d44017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43876, d44017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43876, d44017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43858 q = 1) : d43858 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43877 q = 1) : d363324 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43877, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43877, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43878 q = 1) : d363325 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43878, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43878, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43879 q = 1) : d363326 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43879, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43879, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43891 q = 1) : d363333 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43891, d363333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43891, d363333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100106 (p : Pattern) (ha : d18 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d17 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d18 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d18, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro100107 (p : Pattern) (ha : d308 p = 1) (hb : d1559 p = 1) : d1563 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d1519 q = 1) : d1519 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1540 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1540, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1540, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1541 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1541, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1541, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d1559 q = 1) : d1563 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1559, d1563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1559, d1563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro100108 (p : Pattern) (ha : d308 p = 1) (hb : d34823 p = 1) : d34786 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d1523 q = 1) : d1523 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1524 q = 1) : d2005 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1524, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1524, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1525 q = 1) : d2006 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1525, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1525, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d1547 q = 1) : d1547 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d34823 q = 1) : d34786 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d34823, d34786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d34823, d34786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100109 (p : Pattern) (ha : d308 p = 1) (hb : d43902 p = 1) : d363341 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43852 q = 1) : d43852 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43896 q = 1) : d43853 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43897 q = 1) : d43854 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43858 q = 1) : d43858 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43898 q = 1) : d363338 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43898, d363338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43898, d363338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43899 q = 1) : d43899 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43900 q = 1) : d363339 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43900, d363339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43900, d363339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43901 q = 1) : d363340 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43901, d363340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43901, d363340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d1575 q = 1) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1575, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100107 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d1576 q = 1) : d5129 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1576, d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d1565 q = 1) : d1565 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d1577 q = 1) : d5130 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d5130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1577, d5130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d10129 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100107 q ha hb
    | true =>
      simp only [d10129, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d10130 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10130, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d10131 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10131, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d32178 q = 1) : d5131 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d5131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32178, d5131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d32179 q = 1) : d5132 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d5132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32179, d5132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43902 q = 1) : d363341 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43902, d363341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43902, d363341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100110 (p : Pattern) (ha : d308 p = 1) (hb : d43908 p = 1) : d363347 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43866 q = 1) : d43866 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43881 q = 1) : d363328 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43881, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100104 q ha hb
    | true =>
      simp only [d43881, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43882 q = 1) : d363329 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43882, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43882, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43883 q = 1) : d363330 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43883, d363330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d43883, d363330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43884 q = 1) : d363331 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43884, d363331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43884, d363331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43885 q = 1) : d363332 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43885, d363332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43885, d363332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43892 q = 1) : d363334 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100105 q ha hb
    | true =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43893 q = 1) : d363335 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43894 q = 1) : d363336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43894, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d43894, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43895 q = 1) : d363337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43895, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43895, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43903 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
    | true =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43904 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43905 q = 1) : d363344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43905, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d43905, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43906 q = 1) : d363345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43906, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43906, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43907 q = 1) : d363346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43907, d363346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43907, d363346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43908 q = 1) : d363347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43908, d363347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43908, d363347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100111 (p : Pattern) (ha : d308 p = 1) (hb : d43915 p = 1) : d363351 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43872 q = 1) : d43872 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43852 q = 1) : d43852 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43896 q = 1) : d43853 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100108 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43897 q = 1) : d43854 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43910 q = 1) : d43910 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43911 q = 1) : d363348 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43911, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43911, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43912 q = 1) : d43912 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43913 q = 1) : d363349 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43913, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43913, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43914 q = 1) : d363350 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43914, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43914, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43915 q = 1) : d363351 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43915, d363351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43915, d363351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100112 (p : Pattern) (ha : d308 p = 1) (hb : d43920 p = 1) : d363356 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43852 q = 1) : d43852 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43896 q = 1) : d43853 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43897 q = 1) : d43854 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43910 q = 1) : d43910 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43911 q = 1) : d363348 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43911, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43911, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43912 q = 1) : d43912 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43913 q = 1) : d363349 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43913, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43913, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43914 q = 1) : d363350 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43914, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43914, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d1575 q = 1) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1575, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100107 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d1576 q = 1) : d5129 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1576, d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d1565 q = 1) : d1565 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d1577 q = 1) : d5130 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d5130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1577, d5130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d10129 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100107 q ha hb
    | true =>
      simp only [d10129, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d10130 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10130, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d10131 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10131, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d32178 q = 1) : d5131 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d5131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32178, d5131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d32179 q = 1) : d5132 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d5132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32179, d5132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43920 q = 1) : d363356 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43920, d363356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43920, d363356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100113 (p : Pattern) (ha : d308 p = 1) (hb : d43927 p = 1) : d363363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43916 q = 1) : d363352 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100111 q ha hb
    | true =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43917 q = 1) : d363353 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43918 q = 1) : d363354 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43918, d363354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43918, d363354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43919 q = 1) : d363355 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43919, d363355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43919, d363355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43921 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
    | true =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43922 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43923 q = 1) : d363359 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43923, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43923, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43924 q = 1) : d363360 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43924, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43924, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43925 q = 1) : d363361 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43925, d363361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43925, d363361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43903 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
    | true =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43904 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43905 q = 1) : d363344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43905, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43905, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43906 q = 1) : d363345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43906, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43906, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43926 q = 1) : d363362 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43926, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43926, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43927 q = 1) : d363363 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43927, d363363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43927, d363363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100114 (p : Pattern) (ha : d308 p = 1) (hb : d10134 p = 1) : d270160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d1575 q = 1) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1575, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100107 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d1576 q = 1) : d5129 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1576, d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d1593 q = 1) : d26754 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1593, d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d10129 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100107 q ha hb
    | true =>
      simp only [d10129, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d10130 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10130, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d10131 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10131, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d10132 q = 1) : d26755 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d26755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10132, d26755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d10133 q = 1) : d26756 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d26756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10133, d26756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d10134 q = 1) : d270160 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10134, d270160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10134, d270160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro100115 (p : Pattern) (ha : d308 p = 1) (hb : d43932 p = 1) : d363368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43921 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
    | true =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43922 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43923 q = 1) : d363359 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43923, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43923, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43924 q = 1) : d363360 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43924, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43924, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43931 q = 1) : d363367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43931, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43931, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d10135 q = 1) : d270161 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d270161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100114 q ha hb
    | true =>
      simp only [d10135, d270161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d10137 q = 1) : d270162 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d270162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d270162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d15163 q = 1) : d270163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d270163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15163, d270163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d15164 q = 1) : d270164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d270164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d270164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d15165 q = 1) : d270165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d270165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d270165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43932 q = 1) : d363368 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43932, d363368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43932, d363368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100116 (p : Pattern) (ha : d308 p = 1) (hb : d43939 p = 1) : d363375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43928 q = 1) : d363364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43928, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100110 q ha hb
    | true =>
      simp only [d43928, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43929 q = 1) : d363365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43929, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43929, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43930 q = 1) : d363366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43930, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43930, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43933 q = 1) : d363369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
    | true =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100115 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43934 q = 1) : d363370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43935 q = 1) : d363371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43936 q = 1) : d363372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43936, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43936, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43937 q = 1) : d363373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43937, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43937, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43938 q = 1) : d363374 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43938, d363374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43938, d363374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43939 q = 1) : d363375 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43939, d363375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43939, d363375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100117 (p : Pattern) (ha : d308 p = 1) (hb : d43943 p = 1) : d363379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43933 q = 1) : d363369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
    | true =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100115 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43934 q = 1) : d363370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43935 q = 1) : d363371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43937 q = 1) : d363373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43937, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43937, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43942 q = 1) : d363378 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43942, d363378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43942, d363378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43943 q = 1) : d363379 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43943, d363379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43943, d363379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100118 (p : Pattern) (ha : d308 p = 1) (hb : d43949 p = 1) : d363385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43946 q = 1) : d363382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43947 q = 1) : d363383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43948 q = 1) : d363384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43948, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43948, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43949 q = 1) : d363385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43949, d363385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43949, d363385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100119 (p : Pattern) (ha : d308 p = 1) (hb : d43953 p = 1) : d363389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43950 q = 1) : d363386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43951 q = 1) : d363387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43952 q = 1) : d363388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43952, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43952, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43953 q = 1) : d363389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43953, d363389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43953, d363389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100120 (p : Pattern) (ha : d308 p = 1) (hb : d43959 p = 1) : d363395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43954 q = 1) : d363390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43954, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100118 q ha hb
    | true =>
      simp only [d43954, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100119 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43955 q = 1) : d363391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43955, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43955, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43956 q = 1) : d363392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43956, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43956, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43957 q = 1) : d363393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43957, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43957, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43958 q = 1) : d363394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43958, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43958, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43959 q = 1) : d363395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43959, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43959, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100121 (p : Pattern) (ha : d308 p = 1) (hb : d43962 p = 1) : d363398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43946 q = 1) : d363382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43947 q = 1) : d363383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43948 q = 1) : d363384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43948, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43948, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43962 q = 1) : d363398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43962, d363398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43962, d363398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100122 (p : Pattern) (ha : d308 p = 1) (hb : d43963 p = 1) : d363399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43950 q = 1) : d363386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43951 q = 1) : d363387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43952 q = 1) : d363388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43952, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43952, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43963 q = 1) : d363399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43963, d363399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43963, d363399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100123 (p : Pattern) (ha : d308 p = 1) (hb : d43969 p = 1) : d363405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43954 q = 1) : d363390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43954, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100118 q ha hb
    | true =>
      simp only [d43954, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100119 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43955 q = 1) : d363391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43955, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43955, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43956 q = 1) : d363392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43956, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43956, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43957 q = 1) : d363393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43957, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43957, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43958 q = 1) : d363394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43958, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43958, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43964 q = 1) : d363400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43964, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100121 q ha hb
    | true =>
      simp only [d43964, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100122 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43965 q = 1) : d363401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43965, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43965, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43966 q = 1) : d363402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43966, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43966, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43967 q = 1) : d363403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43967, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43967, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43968 q = 1) : d363404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43968, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43968, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43969 q = 1) : d363405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43969, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43969, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100124 (p : Pattern) (ha : d308 p = 1) (hb : d44216 p = 1) : d363498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43954 q = 1) : d363390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43954, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100118 q ha hb
    | true =>
      simp only [d43954, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100119 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43955 q = 1) : d363391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43955, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43955, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43956 q = 1) : d363392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43956, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43956, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43957 q = 1) : d363393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43957, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43957, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43958 q = 1) : d363394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43958, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43958, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44211 q = 1) : d363493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44211, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100119 q ha hb
    | true =>
      simp only [d44211, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44212 q = 1) : d363494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44212, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44212, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44213 q = 1) : d363495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44213, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44213, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44214 q = 1) : d363496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44214, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44214, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44215 q = 1) : d363497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44215, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44215, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44216 q = 1) : d363498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44216, d363498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44216, d363498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100125 (p : Pattern) (ha : d308 p = 1) (hb : d44222 p = 1) : d363504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44211 q = 1) : d363493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44211, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100119 q ha hb
    | true =>
      simp only [d44211, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44212 q = 1) : d363494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44212, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44212, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44213 q = 1) : d363495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44213, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44213, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44214 q = 1) : d363496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44214, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44214, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44215 q = 1) : d363497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44215, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44215, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44217 q = 1) : d363499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44217, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100122 q ha hb
    | true =>
      simp only [d44217, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44218 q = 1) : d363500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44218, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44218, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44219 q = 1) : d363501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44219, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44219, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44220 q = 1) : d363502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44220, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44220, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44221 q = 1) : d363503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44221, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44221, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44222 q = 1) : d363504 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44222, d363504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44222, d363504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100126 (p : Pattern) (ha : d308 p = 1) (hb : d44231 p = 1) : d363513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44217 q = 1) : d363499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44217, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100122 q ha hb
    | true =>
      simp only [d44217, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44218 q = 1) : d363500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44218, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44218, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44219 q = 1) : d363501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44219, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44219, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44220 q = 1) : d363502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44220, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44220, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44221 q = 1) : d363503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44221, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44221, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44231 q = 1) : d363513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44231, d363513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44231, d363513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100127 (p : Pattern) (ha : d308 p = 1) (hb : d44294 p = 1) : d363559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44285 q = 1) : d363550 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44285, d363550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44285, d363550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100111 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43916 q = 1) : d363352 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100111 q ha hb
    | true =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44286 q = 1) : d363551 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44286, d363551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44286, d363551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43917 q = 1) : d363353 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44287 q = 1) : d363552 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44287, d363552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44287, d363552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44288 q = 1) : d363553 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44288, d363553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44288, d363553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44289 q = 1) : d363554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44289, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44289, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43921 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
    | true =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44290 q = 1) : d363555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44290, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44290, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43922 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44291 q = 1) : d363556 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44291, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44291, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44292 q = 1) : d363557 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44292, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44292, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44293 q = 1) : d363558 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44293, d363558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44293, d363558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d44265 q = 1) : d363530 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44265, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44265, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43903 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
    | true =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d44266 q = 1) : d363531 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44266, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44266, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43904 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d44267 q = 1) : d363532 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44267, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44267, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d44268 q = 1) : d363533 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44268, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44268, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d44279 q = 1) : d363544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44279, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44279, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d44294 q = 1) : d363559 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44294, d363559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44294, d363559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100128 (p : Pattern) (ha : d308 p = 1) (hb : d44299 p = 1) : d363564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44289 q = 1) : d363554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44289, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44289, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43921 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
    | true =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44290 q = 1) : d363555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44290, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44290, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43922 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44291 q = 1) : d363556 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44291, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44291, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44292 q = 1) : d363557 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44292, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44292, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44298 q = 1) : d363563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44298, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44298, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d15412 q = 1) : d270386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d270386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15412, d270386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100114 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d10135 q = 1) : d270161 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d270161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100114 q ha hb
    | true =>
      simp only [d10135, d270161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d15413 q = 1) : d270387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d270387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d270387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d10137 q = 1) : d270162 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d270162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d270162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d15414 q = 1) : d270388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d270388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d270388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d15415 q = 1) : d270389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d270389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d270389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d15416 q = 1) : d270390 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d270390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d270390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44299 q = 1) : d363564 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44299, d363564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44299, d363564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100129 (p : Pattern) (ha : d308 p = 1) (hb : d44318 p = 1) : d363583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44300 q = 1) : d363565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
    | true =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100128 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44301 q = 1) : d363566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44302 q = 1) : d363567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44308 q = 1) : d363573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44308, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44308, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44317 q = 1) : d363582 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44317, d363582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44317, d363582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44318 q = 1) : d363583 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44318, d363583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44318, d363583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100130 (p : Pattern) (ha : d308 p = 1) (hb : d44418 p = 1) : d363615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44319 q = 1) : d363584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44319, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100129 q ha hb
    | true =>
      simp only [d44319, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44320 q = 1) : d363585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44320, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44320, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44415 q = 1) : d363612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44415, d363612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44415, d363612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44416 q = 1) : d363613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44416, d363613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44416, d363613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44417 q = 1) : d363614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44417, d363614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44417, d363614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44418 q = 1) : d363615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44418, d363615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44418, d363615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100131 (p : Pattern) (ha : d308 p = 1) (hb : d44424 p = 1) : d363621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44419 q = 1) : d363616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44419, d363616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100130 q ha hb
    | true =>
      simp only [d44419, d363616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44420 q = 1) : d363617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44420, d363617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44420, d363617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44421 q = 1) : d363618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44421, d363618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44421, d363618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44422 q = 1) : d363619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44422, d363619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44422, d363619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44423 q = 1) : d363620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44423, d363620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44423, d363620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44424 q = 1) : d363621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44424, d363621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44424, d363621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100132 (p : Pattern) (ha : d308 p = 1) (hb : d43974 p = 1) : d363410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43946 q = 1) : d363382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43947 q = 1) : d363383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43973 q = 1) : d363409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43973, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43973, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43974 q = 1) : d363410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43974, d363410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43974, d363410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100133 (p : Pattern) (ha : d308 p = 1) (hb : d43976 p = 1) : d363412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43950 q = 1) : d363386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43951 q = 1) : d363387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43975 q = 1) : d363411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43975, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43975, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43976 q = 1) : d363412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43976, d363412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43976, d363412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100134 (p : Pattern) (ha : d308 p = 1) (hb : d43983 p = 1) : d363419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43946 q = 1) : d363382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43981 q = 1) : d363417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43981, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43981, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43982 q = 1) : d363418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43982, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43982, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43983 q = 1) : d363419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43983, d363419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43983, d363419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100135 (p : Pattern) (ha : d308 p = 1) (hb : d43986 p = 1) : d363422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43950 q = 1) : d363386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43984 q = 1) : d363420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43984, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43984, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43985 q = 1) : d363421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43985, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43985, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43986 q = 1) : d363422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43986, d363422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43986, d363422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100136 (p : Pattern) (ha : d308 p = 1) (hb : d44012 p = 1) : d363427 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d44003 q = 1) : d44003 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44010 q = 1) : d44010 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43892 q = 1) : d363334 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100105 q ha hb
    | true =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43893 q = 1) : d363335 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43894 q = 1) : d363336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43894, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d43894, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43895 q = 1) : d363337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43895, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43895, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44011 q = 1) : d363426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44011, d363426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44011, d363426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44012 q = 1) : d363427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44012, d363427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44012, d363427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100137 (p : Pattern) (ha : d308 p = 1) (hb : d44021 p = 1) : d363431 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d44020 q = 1) : d44020 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43874 q = 1) : d43874 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43875 q = 1) : d44016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43875, d44016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43875, d44016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100103 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43876 q = 1) : d44017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43876, d44017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43876, d44017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43858 q = 1) : d43858 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43877 q = 1) : d363324 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43877, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43877, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43878 q = 1) : d363325 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43878, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43878, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43879 q = 1) : d363326 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43879, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43879, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44021 q = 1) : d363431 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44021, d363431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44021, d363431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100138 (p : Pattern) (ha : d308 p = 1) (hb : d44027 p = 1) : d363437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44022 q = 1) : d363432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44022, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100137 q ha hb
    | true =>
      simp only [d44022, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44023 q = 1) : d363433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44023, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44023, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44024 q = 1) : d363434 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44024, d363434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44024, d363434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44025 q = 1) : d363435 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44025, d363435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44025, d363435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43903 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
    | true =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43904 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43905 q = 1) : d363344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43905, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43905, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43906 q = 1) : d363345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43906, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43906, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44026 q = 1) : d363436 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44026, d363436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44026, d363436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43926 q = 1) : d363362 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43926, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43926, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44027 q = 1) : d363437 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44027, d363437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44027, d363437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100139 (p : Pattern) (ha : d308 p = 1) (hb : d44033 p = 1) : d363443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44013 q = 1) : d363428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44013, d363428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100136 q ha hb
    | true =>
      simp only [d44013, d363428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100110 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44014 q = 1) : d363429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44014, d363429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44014, d363429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44015 q = 1) : d363430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44015, d363430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44015, d363430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44028 q = 1) : d363438 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44028, d363438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100110 q ha hb
    | true =>
      simp only [d44028, d363438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100138 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44029 q = 1) : d363439 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44029, d363439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44029, d363439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44030 q = 1) : d363440 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44030, d363440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44030, d363440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44031 q = 1) : d363441 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44031, d363441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44031, d363441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43928 q = 1) : d363364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43928, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100110 q ha hb
    | true =>
      simp only [d43928, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43929 q = 1) : d363365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43929, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43929, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43930 q = 1) : d363366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43930, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43930, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43933 q = 1) : d363369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
    | true =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100115 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43934 q = 1) : d363370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43935 q = 1) : d363371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43936 q = 1) : d363372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43936, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43936, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44032 q = 1) : d363442 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44032, d363442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44032, d363442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d44033 q = 1) : d363443 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44033, d363443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44033, d363443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100140 (p : Pattern) (ha : d308 p = 1) (hb : d44039 p = 1) : d363449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44034 q = 1) : d363444 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44034, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100139 q ha hb
    | true =>
      simp only [d44034, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44035 q = 1) : d363445 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44035, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44035, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44036 q = 1) : d363446 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44036, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44036, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44037 q = 1) : d363447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44037, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44037, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44038 q = 1) : d363448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44038, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44038, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44039 q = 1) : d363449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44039, d363449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44039, d363449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100141 (p : Pattern) (ha : d308 p = 1) (hb : d44154 p = 1) : d363341 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43852 q = 1) : d43852 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43896 q = 1) : d43853 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43897 q = 1) : d43854 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43858 q = 1) : d43858 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43898 q = 1) : d363338 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43898, d363338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43898, d363338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43899 q = 1) : d43899 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43900 q = 1) : d363339 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43900, d363339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43900, d363339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43901 q = 1) : d363340 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43901, d363340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43901, d363340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d5132 q = 1) : d5132 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44154 q = 1) : d363341 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44154, d363341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44154, d363341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100142 (p : Pattern) (ha : d308 p = 1) (hb : d44160 p = 1) : d363363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43916 q = 1) : d363352 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100111 q ha hb
    | true =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43917 q = 1) : d363353 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43918 q = 1) : d363354 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43918, d363354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43918, d363354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43919 q = 1) : d363355 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43919, d363355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43919, d363355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43921 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
    | true =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43922 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43923 q = 1) : d363359 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43923, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43923, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43924 q = 1) : d363360 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43924, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43924, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43925 q = 1) : d363361 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43925, d363361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43925, d363361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44155 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44155, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100141 q ha hb
    | true =>
      simp only [d44155, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44156 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44156, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44156, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44157 q = 1) : d363344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44157, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44157, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44158 q = 1) : d363345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44158, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44158, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d44159 q = 1) : d363362 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44159, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44159, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44160 q = 1) : d363363 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44160, d363363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44160, d363363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100143 (p : Pattern) (ha : d308 p = 1) (hb : d44161 p = 1) : d363356 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43852 q = 1) : d43852 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43896 q = 1) : d43853 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43896, d43853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43897 q = 1) : d43854 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43897, d43854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43910 q = 1) : d43910 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43911 q = 1) : d363348 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43911, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43911, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43912 q = 1) : d43912 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43913 q = 1) : d363349 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43913, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43913, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43914 q = 1) : d363350 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43914, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43914, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d5132 q = 1) : d5132 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44161 q = 1) : d363356 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44161, d363356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44161, d363356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100144 (p : Pattern) (ha : d308 p = 1) (hb : d44167 p = 1) : d363452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44162 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44162, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100143 q ha hb
    | true =>
      simp only [d44162, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44163 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44163, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44163, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44164 q = 1) : d363359 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44164, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44164, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44165 q = 1) : d363360 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44165, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44165, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44166 q = 1) : d363367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44166, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44166, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44167 q = 1) : d363452 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44167, d363452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44167, d363452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100145 (p : Pattern) (ha : d308 p = 1) (hb : d44173 p = 1) : d363458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43928 q = 1) : d363364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43928, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100110 q ha hb
    | true =>
      simp only [d43928, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43929 q = 1) : d363365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43929, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43929, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43930 q = 1) : d363366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43930, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43930, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43933 q = 1) : d363369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100113 q ha hb
    | true =>
      simp only [d43933, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100115 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43934 q = 1) : d363370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43934, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43935 q = 1) : d363371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43935, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43936 q = 1) : d363372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43936, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43936, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44168 q = 1) : d363453 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44168, d363453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100142 q ha hb
    | true =>
      simp only [d44168, d363453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100144 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44169 q = 1) : d363454 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44169, d363454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44169, d363454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44170 q = 1) : d363455 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44170, d363455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44170, d363455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44171 q = 1) : d363456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44171, d363456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44171, d363456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44172 q = 1) : d363457 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44172, d363457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44172, d363457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44173 q = 1) : d363458 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44173, d363458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44173, d363458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100146 (p : Pattern) (ha : d308 p = 1) (hb : d44179 p = 1) : d363464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44174 q = 1) : d363459 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44174, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100145 q ha hb
    | true =>
      simp only [d44174, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44175 q = 1) : d363460 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44175, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44175, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44176 q = 1) : d363461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44176, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44176, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44177 q = 1) : d363462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44177, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44177, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44178 q = 1) : d363463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44178, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44178, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44179 q = 1) : d363464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44179, d363464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44179, d363464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100147 (p : Pattern) (ha : d308 p = 1) (hb : d309971 p = 1) : d363470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43977 q = 1) : d363413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43977, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100132 q ha hb
    | true =>
      simp only [d43977, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100133 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43978 q = 1) : d363414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43978, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43978, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43979 q = 1) : d363415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43979, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43979, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43980 q = 1) : d363416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43980, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43980, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43987 q = 1) : d363423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43987, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100134 q ha hb
    | true =>
      simp only [d43987, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100135 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43988 q = 1) : d363424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43988, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43988, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43989 q = 1) : d363425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43989, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43989, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44040 q = 1) : d363450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44040, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100140 q ha hb
    | true =>
      simp only [d44040, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100118 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309967 q = 1) : d363451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309967, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44180 q = 1) : d363465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44180, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100146 q ha hb
    | true =>
      simp only [d44180, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44181 q = 1) : d363466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44181, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44181, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309968 q = 1) : d363467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309968, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309969 q = 1) : d363468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309969, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309970 q = 1) : d363469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309970, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309971 q = 1) : d363470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309971, d363470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309971, d363470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100148 (p : Pattern) (ha : d308 p = 1) (hb : d44186 p = 1) : d363471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43946 q = 1) : d363382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43947 q = 1) : d363383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43947, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43973 q = 1) : d363409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43973, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43973, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44186 q = 1) : d363471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44186, d363471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44186, d363471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100149 (p : Pattern) (ha : d308 p = 1) (hb : d44187 p = 1) : d363472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43950 q = 1) : d363386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43951 q = 1) : d363387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43951, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43975 q = 1) : d363411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43975, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43975, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44187 q = 1) : d363472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44187, d363472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44187, d363472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100150 (p : Pattern) (ha : d308 p = 1) (hb : d44192 p = 1) : d363477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43946 q = 1) : d363382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43946, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43981 q = 1) : d363417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43981, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43981, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43982 q = 1) : d363418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43982, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43982, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44192 q = 1) : d363477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44192, d363477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44192, d363477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100151 (p : Pattern) (ha : d308 p = 1) (hb : d44193 p = 1) : d363478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43944 q = 1) : d363380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100117 q ha hb
    | true =>
      simp only [d43944, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43945 q = 1) : d363381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43945, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43950 q = 1) : d363386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43950, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43984 q = 1) : d363420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43984, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43984, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43985 q = 1) : d363421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43985, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43985, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44193 q = 1) : d363478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44193, d363478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44193, d363478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100152 (p : Pattern) (ha : d308 p = 1) (hb : d44197 p = 1) : d363482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44034 q = 1) : d363444 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44034, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100139 q ha hb
    | true =>
      simp only [d44034, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44035 q = 1) : d363445 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44035, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44035, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43940 q = 1) : d363376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100116 q ha hb
    | true =>
      simp only [d43940, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43941 q = 1) : d363377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43941, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44036 q = 1) : d363446 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44036, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44036, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44037 q = 1) : d363447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44037, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44037, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44038 q = 1) : d363448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44038, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44038, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44197 q = 1) : d363482 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44197, d363482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44197, d363482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100153 (p : Pattern) (ha : d308 p = 1) (hb : d44203 p = 1) : d363485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44174 q = 1) : d363459 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44174, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100145 q ha hb
    | true =>
      simp only [d44174, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44175 q = 1) : d363460 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44175, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44175, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44176 q = 1) : d363461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44176, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44176, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44177 q = 1) : d363462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44177, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44177, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44178 q = 1) : d363463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44178, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44178, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44203 q = 1) : d363485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44203, d363485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44203, d363485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100154 (p : Pattern) (ha : d308 p = 1) (hb : d309976 p = 1) : d363491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43977 q = 1) : d363413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43977, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100132 q ha hb
    | true =>
      simp only [d43977, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100133 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43978 q = 1) : d363414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43978, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43978, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43979 q = 1) : d363415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43979, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43979, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43980 q = 1) : d363416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43980, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43980, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43987 q = 1) : d363423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43987, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100134 q ha hb
    | true =>
      simp only [d43987, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100135 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43988 q = 1) : d363424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43988, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43988, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43989 q = 1) : d363425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43989, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43989, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44040 q = 1) : d363450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44040, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100140 q ha hb
    | true =>
      simp only [d44040, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100118 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309967 q = 1) : d363451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309967, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44180 q = 1) : d363465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44180, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100146 q ha hb
    | true =>
      simp only [d44180, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44181 q = 1) : d363466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44181, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44181, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309968 q = 1) : d363467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309968, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309969 q = 1) : d363468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309969, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309970 q = 1) : d363469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309970, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44188 q = 1) : d363473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44188, d363473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100148 q ha hb
    | true =>
      simp only [d44188, d363473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100149 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d44189 q = 1) : d363474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44189, d363474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44189, d363474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d44190 q = 1) : d363475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44190, d363475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44190, d363475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d44191 q = 1) : d363476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44191, d363476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44191, d363476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d44194 q = 1) : d363479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44194, d363479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100150 q ha hb
    | true =>
      simp only [d44194, d363479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100151 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d44195 q = 1) : d363480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44195, d363480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44195, d363480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d44196 q = 1) : d363481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44196, d363481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d44196, d363481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d44198 q = 1) : d363483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44198, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100152 q ha hb
    | true =>
      simp only [d44198, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100121 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309972 q = 1) : d363484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309972, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d44204 q = 1) : d363486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44204, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100153 q ha hb
    | true =>
      simp only [d44204, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d44205 q = 1) : d363487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44205, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d44205, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d309973 q = 1) : d363488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309973, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d309974 q = 1) : d363489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309974, d363489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309974, d363489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d309975 q = 1) : d363490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309975, d363490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309975, d363490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d309976 q = 1) : d363491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309976, d363491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309976, d363491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro100155 (p : Pattern) (ha : d308 p = 1) (hb : d309983 p = 1) : d363511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44198 q = 1) : d363483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44198, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100152 q ha hb
    | true =>
      simp only [d44198, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100121 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309972 q = 1) : d363484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309972, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44204 q = 1) : d363486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44204, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100153 q ha hb
    | true =>
      simp only [d44204, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44205 q = 1) : d363487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44205, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44205, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309973 q = 1) : d363488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309973, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309981 q = 1) : d363509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309981, d363509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309981, d363509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309982 q = 1) : d363510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309982, d363510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309982, d363510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309983 q = 1) : d363511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309983, d363511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309983, d363511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100156 (p : Pattern) (ha : d308 p = 1) (hb : d44255 p = 1) : d363524 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d44245 q = 1) : d44245 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44249 q = 1) : d44249 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44250 q = 1) : d363519 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44250, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d44250, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100105 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43892 q = 1) : d363334 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100105 q ha hb
    | true =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44251 q = 1) : d363520 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44251, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44251, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43893 q = 1) : d363335 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44252 q = 1) : d363521 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44252, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44252, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44253 q = 1) : d363522 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44253, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44253, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44254 q = 1) : d363523 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44254, d363523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44254, d363523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44255 q = 1) : d363524 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44255, d363524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44255, d363524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100157 (p : Pattern) (ha : d308 p = 1) (hb : d44270 p = 1) : d363535 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d44259 q = 1) : d44259 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44260 q = 1) : d363525 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44260, d363525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d44260, d363525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100104 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43881 q = 1) : d363328 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43881, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100104 q ha hb
    | true =>
      simp only [d43881, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44261 q = 1) : d363526 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44261, d363526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44261, d363526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43882 q = 1) : d363329 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43882, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43882, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44262 q = 1) : d363527 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44262, d363527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44262, d363527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44263 q = 1) : d363528 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44263, d363528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44263, d363528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44264 q = 1) : d363529 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44264, d363529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44264, d363529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44250 q = 1) : d363519 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44250, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d44250, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100105 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43892 q = 1) : d363334 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100105 q ha hb
    | true =>
      simp only [d43892, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44251 q = 1) : d363520 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44251, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44251, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43893 q = 1) : d363335 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43893, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44252 q = 1) : d363521 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44252, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44252, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d44253 q = 1) : d363522 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44253, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44253, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44265 q = 1) : d363530 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44265, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d44265, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43903 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
    | true =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d44266 q = 1) : d363531 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44266, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44266, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43904 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d44267 q = 1) : d363532 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44267, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d44267, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d44268 q = 1) : d363533 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44268, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44268, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d44269 q = 1) : d363534 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44269, d363534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44269, d363534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d44270 q = 1) : d363535 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44270, d363535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44270, d363535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro100158 (p : Pattern) (ha : d308 p = 1) (hb : d44280 p = 1) : d363545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44274 q = 1) : d363539 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44274, d363539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44274, d363539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100137 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44022 q = 1) : d363432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44022, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100137 q ha hb
    | true =>
      simp only [d44022, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44275 q = 1) : d363540 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44275, d363540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44275, d363540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44023 q = 1) : d363433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44023, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44023, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44276 q = 1) : d363541 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44276, d363541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44276, d363541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44277 q = 1) : d363542 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44277, d363542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44277, d363542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44265 q = 1) : d363530 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44265, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44265, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43903 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100109 q ha hb
    | true =>
      simp only [d43903, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44266 q = 1) : d363531 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44266, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44266, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43904 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43904, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44267 q = 1) : d363532 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44267, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44267, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44268 q = 1) : d363533 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44268, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44268, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44278 q = 1) : d363543 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44278, d363543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44278, d363543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d44279 q = 1) : d363544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44279, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44279, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44280 q = 1) : d363545 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44280, d363545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44280, d363545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100159 (p : Pattern) (ha : d308 p = 1) (hb : d44305 p = 1) : d363570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44271 q = 1) : d363536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44271, d363536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100156 q ha hb
    | true =>
      simp only [d44271, d363536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100157 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44272 q = 1) : d363537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44272, d363537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44272, d363537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44273 q = 1) : d363538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44273, d363538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44273, d363538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44281 q = 1) : d363546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44281, d363546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100157 q ha hb
    | true =>
      simp only [d44281, d363546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100158 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44282 q = 1) : d363547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44282, d363547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44282, d363547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44283 q = 1) : d363548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44283, d363548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44283, d363548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44284 q = 1) : d363549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44284, d363549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44284, d363549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44295 q = 1) : d363560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44295, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100157 q ha hb
    | true =>
      simp only [d44295, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44296 q = 1) : d363561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44296, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44296, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44297 q = 1) : d363562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44297, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44297, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44300 q = 1) : d363565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
    | true =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100128 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44301 q = 1) : d363566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44302 q = 1) : d363567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d44303 q = 1) : d363568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44303, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44303, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44304 q = 1) : d363569 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44304, d363569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44304, d363569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d44305 q = 1) : d363570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44305, d363570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44305, d363570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100160 (p : Pattern) (ha : d308 p = 1) (hb : d44310 p = 1) : d363575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44295 q = 1) : d363560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44295, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100157 q ha hb
    | true =>
      simp only [d44295, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44296 q = 1) : d363561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44296, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44296, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44297 q = 1) : d363562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44297, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44297, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44300 q = 1) : d363565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
    | true =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100128 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44301 q = 1) : d363566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44302 q = 1) : d363567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44303 q = 1) : d363568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44303, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44303, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44308 q = 1) : d363573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44308, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44308, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44309 q = 1) : d363574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44309, d363574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44309, d363574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44310 q = 1) : d363575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44310, d363575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44310, d363575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100161 (p : Pattern) (ha : d308 p = 1) (hb : d44316 p = 1) : d363581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44306 q = 1) : d363571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44306, d363571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100159 q ha hb
    | true =>
      simp only [d44306, d363571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44307 q = 1) : d363572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44307, d363572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44307, d363572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44311 q = 1) : d363576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44311, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100160 q ha hb
    | true =>
      simp only [d44311, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44312 q = 1) : d363577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44312, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44312, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44313 q = 1) : d363578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44313, d363578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44313, d363578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44314 q = 1) : d363579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44314, d363579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44314, d363579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44315 q = 1) : d363580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44315, d363580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44315, d363580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44316 q = 1) : d363581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44316, d363581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44316, d363581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100162 (p : Pattern) (ha : d308 p = 1) (hb : d44324 p = 1) : d363589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44311 q = 1) : d363576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44311, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100160 q ha hb
    | true =>
      simp only [d44311, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44312 q = 1) : d363577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44312, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44312, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44319 q = 1) : d363584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44319, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100129 q ha hb
    | true =>
      simp only [d44319, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44320 q = 1) : d363585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44320, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44320, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44321 q = 1) : d363586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44321, d363586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44321, d363586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44322 q = 1) : d363587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44322, d363587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44322, d363587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44323 q = 1) : d363588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44323, d363588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44323, d363588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44324 q = 1) : d363589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44324, d363589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44324, d363589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100163 (p : Pattern) (ha : d308 p = 1) (hb : d44389 p = 1) : d363559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44285 q = 1) : d363550 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44285, d363550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44285, d363550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100111 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43916 q = 1) : d363352 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100111 q ha hb
    | true =>
      simp only [d43916, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44286 q = 1) : d363551 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44286, d363551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44286, d363551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43917 q = 1) : d363353 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43917, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44287 q = 1) : d363552 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44287, d363552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44287, d363552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44288 q = 1) : d363553 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44288, d363553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44288, d363553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44289 q = 1) : d363554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44289, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44289, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43921 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100112 q ha hb
    | true =>
      simp only [d43921, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44290 q = 1) : d363555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44290, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44290, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43922 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43922, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44291 q = 1) : d363556 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44291, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44291, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44292 q = 1) : d363557 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44292, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44292, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44293 q = 1) : d363558 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44293, d363558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44293, d363558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d44384 q = 1) : d363530 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44384, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44384, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100141 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d44155 q = 1) : d363342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44155, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100141 q ha hb
    | true =>
      simp only [d44155, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d44385 q = 1) : d363531 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44385, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44385, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d44156 q = 1) : d363343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44156, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44156, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d44386 q = 1) : d363532 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44386, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44386, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d44387 q = 1) : d363533 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44387, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44387, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d44388 q = 1) : d363544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44388, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44388, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d44389 q = 1) : d363559 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44389, d363559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44389, d363559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100164 (p : Pattern) (ha : d308 p = 1) (hb : d44395 p = 1) : d363592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44390 q = 1) : d363554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44390, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44390, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100143 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44162 q = 1) : d363357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44162, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100143 q ha hb
    | true =>
      simp only [d44162, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44391 q = 1) : d363555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44391, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44391, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44163 q = 1) : d363358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44163, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44163, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44392 q = 1) : d363556 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44392, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44392, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44393 q = 1) : d363557 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44393, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44393, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44394 q = 1) : d363563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44394, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44394, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44395 q = 1) : d363592 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44395, d363592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44395, d363592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100165 (p : Pattern) (ha : d308 p = 1) (hb : d44401 p = 1) : d363598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44295 q = 1) : d363560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44295, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100157 q ha hb
    | true =>
      simp only [d44295, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44296 q = 1) : d363561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44296, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44296, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44297 q = 1) : d363562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44297, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44297, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44300 q = 1) : d363565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100127 q ha hb
    | true =>
      simp only [d44300, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100128 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44301 q = 1) : d363566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44301, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44302 q = 1) : d363567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44302, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44303 q = 1) : d363568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44303, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44303, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d44396 q = 1) : d363593 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44396, d363593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100163 q ha hb
    | true =>
      simp only [d44396, d363593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100164 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d44397 q = 1) : d363594 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44397, d363594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44397, d363594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d44398 q = 1) : d363595 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44398, d363595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44398, d363595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d44399 q = 1) : d363596 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44399, d363596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44399, d363596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44400 q = 1) : d363597 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44400, d363597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44400, d363597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d44401 q = 1) : d363598 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44401, d363598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44401, d363598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100166 (p : Pattern) (ha : d308 p = 1) (hb : d44407 p = 1) : d363604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44402 q = 1) : d363599 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44402, d363599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100165 q ha hb
    | true =>
      simp only [d44402, d363599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44403 q = 1) : d363600 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44403, d363600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44403, d363600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44404 q = 1) : d363601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44404, d363601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44404, d363601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44405 q = 1) : d363602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44405, d363602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44405, d363602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d44406 q = 1) : d363603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44406, d363603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44406, d363603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44407 q = 1) : d363604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44407, d363604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44407, d363604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100167 (p : Pattern) (ha : d308 p = 1) (hb : d309993 p = 1) : d363610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d44325 q = 1) : d363590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44325, d363590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100161 q ha hb
    | true =>
      simp only [d44325, d363590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100162 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309989 q = 1) : d363591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309989, d363591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309989, d363591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d44408 q = 1) : d363605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44408, d363605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100166 q ha hb
    | true =>
      simp only [d44408, d363605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d44409 q = 1) : d363606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44409, d363606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44409, d363606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309990 q = 1) : d363607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309990, d363607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309990, d363607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309991 q = 1) : d363608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309991, d363608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309991, d363608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309992 q = 1) : d363609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309992, d363609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309992, d363609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309993 q = 1) : d363610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309993, d363610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309993, d363610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100168 (p : Pattern) (ha : d308 p = 1) (hb : d309999 p = 1) : d363627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43960 q = 1) : d363396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43960, d363396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43960, d363396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100120 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43961 q = 1) : d363397 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43961, d363397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43961, d363397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43970 q = 1) : d363406 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43970, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100120 q ha hb
    | true =>
      simp only [d43970, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100123 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43971 q = 1) : d363407 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43971, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43971, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43972 q = 1) : d363408 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d43972, d363408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43972, d363408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309977 q = 1) : d363492 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309977, d363492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100147 q ha hb
    | true =>
      simp only [d309977, d363492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100154 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d44223 q = 1) : d363505 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44223, d363505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100124 q ha hb
    | true =>
      simp only [d44223, d363505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100125 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309978 q = 1) : d363506 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309978, d363506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309978, d363506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309979 q = 1) : d363507 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309979, d363507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309979, d363507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d309980 q = 1) : d363508 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309980, d363508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309980, d363508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d309984 q = 1) : d363512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309984, d363512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309984, d363512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100155 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44232 q = 1) : d363514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44232, d363514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44232, d363514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100126 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309985 q = 1) : d363515 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309985, d363515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309985, d363515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309986 q = 1) : d363516 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309986, d363516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309986, d363516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309987 q = 1) : d363517 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309987, d363517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309987, d363517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d309988 q = 1) : d363518 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309988, d363518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309988, d363518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d309994 q = 1) : d363611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309994, d363611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309994, d363611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100167 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d44425 q = 1) : d363622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44425, d363622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44425, d363622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100131 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d309995 q = 1) : d363623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309995, d363623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309995, d363623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d309996 q = 1) : d363624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309996, d363624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309996, d363624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d309997 q = 1) : d363625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309997, d363625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309997, d363625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d309998 q = 1) : d363626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309998, d363626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309998, d363626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309999 q = 1) : d363627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309999, d363627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309999, d363627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100169 (p : Pattern) (ha : d308 p = 1) (hb : d310005 p = 1) : d363633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d310000 q = 1) : d363628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d310000, d363628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310000, d363628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100168 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d310001 q = 1) : d363629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d310001, d363629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310001, d363629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d310002 q = 1) : d363630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d310002, d363630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310002, d363630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d310003 q = 1) : d363631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d310003, d363631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310003, d363631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d310004 q = 1) : d363632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d310004, d363632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310004, d363632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d310005 q = 1) : d363633 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d310005, d363633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310005, d363633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100170 (p : Pattern) (ha : d310011 p = 1) (hb : d363232 p = 1) : d363639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d310006 q = 1) : d363634 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d310006, d363634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d310006, d363634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100169 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d310007 q = 1) : d363635 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d310007, d363635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d310007, d363635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d310008 q = 1) : d363636 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d310008, d363636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d310008, d363636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310009 q = 1) (hb : d363231 q = 1) : d363637 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d363231, d363637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310009, d363231, d363637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310010 q = 1) (hb : d363232 q = 1) : d363638 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d363232, d363638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310010, d363232, d363638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d363232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310011 q = 1) (hb : d363232 q = 1) : d363639 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d363639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310011, d363639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100171 (p : Pattern) (ha : d310017 p = 1) (hb : d363232 p = 1) : d363645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d363232 q = 1) : d363640 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d363640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100170 q ha hb
    | true =>
      simp only [d310012, d363640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d363232 q = 1) : d363641 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d363641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d363641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d363232 q = 1) : d363642 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d363642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d363642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d363232 q = 1) : d363643 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d363643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d363643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d363232 q = 1) : d363644 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d363644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d363644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d363232 q = 1) : d363645 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d363645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d363645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100172 (p : Pattern) (ha : d310023 p = 1) (hb : d363235 p = 1) : d363651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d363232 q = 1) : d363646 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d363646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100171 q ha hb
    | true =>
      simp only [d310018, d363646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d363232 q = 1) : d363647 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d363647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d363647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d310020 q = 1) (hb : d363233 q = 1) : d363648 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d363233, d363648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d363233, d363648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310021 q = 1) (hb : d363234 q = 1) : d363649 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d363234, d363649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310021, d363234, d363649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d310022 q = 1) (hb : d363235 q = 1) : d363650 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d363235, d363650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310022, d363235, d363650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d310023 q = 1) (hb : d363235 q = 1) : d363651 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d363651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310023, d363651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100173 (p : Pattern) (ha : d310029 p = 1) (hb : d363235 p = 1) : d363657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d363235 q = 1) : d363652 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d363652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100172 q ha hb
    | true =>
      simp only [d310024, d363652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d363235 q = 1) : d363653 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d363653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d363653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d363235 q = 1) : d363654 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d363654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d363654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d363235 q = 1) : d363655 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d363655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d363655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d363235 q = 1) : d363656 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d363656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d363656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d363235 q = 1) : d363657 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d363657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d363657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100174 (p : Pattern) (ha : d310035 p = 1) (hb : d363235 p = 1) : d363663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d363235 q = 1) : d363658 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d363658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100173 q ha hb
    | true =>
      simp only [d310030, d363658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d363235 q = 1) : d363659 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d363659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d363659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d363235 q = 1) : d363660 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d363660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d363660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d363235 q = 1) : d363661 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d363661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d363661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d363235 q = 1) : d363662 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d363662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d363662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d363235 q = 1) : d363663 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d363663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d363663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100175 (p : Pattern) (ha : d310041 p = 1) (hb : d363235 p = 1) : d363669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d363235 q = 1) : d363664 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d363664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100174 q ha hb
    | true =>
      simp only [d310036, d363664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d363235 q = 1) : d363665 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d363665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d363665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d363235 q = 1) : d363666 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d363666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d363666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d363235 q = 1) : d363667 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d363667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d363667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d363235 q = 1) : d363668 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d363668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d363668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d363235 q = 1) : d363669 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d363669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d363669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100176 (p : Pattern) (ha : d310047 p = 1) (hb : d363235 p = 1) : d363675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d363235 q = 1) : d363670 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d363670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100175 q ha hb
    | true =>
      simp only [d310042, d363670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d363235 q = 1) : d363671 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d363671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d363671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d363235 q = 1) : d363672 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d363672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d363672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d363235 q = 1) : d363673 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d363673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d363673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d363235 q = 1) : d363674 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d363674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d363674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d363235 q = 1) : d363675 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d363675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d363675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100177 (p : Pattern) (ha : d310053 p = 1) (hb : d363235 p = 1) : d363681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d363235 q = 1) : d363676 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d363676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100176 q ha hb
    | true =>
      simp only [d310048, d363676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d363235 q = 1) : d363677 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d363677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d363677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d363235 q = 1) : d363678 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d363678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d363678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d363235 q = 1) : d363679 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d363679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d363679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d363235 q = 1) : d363680 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d363680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d363680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d363235 q = 1) : d363681 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d363681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d363681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100178 (p : Pattern) (ha : d2007 p = 1) (hb : d361882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1523 q = 1) (hb : d273807 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2005 q = 1) (hb : d361620 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d361620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2005, d361620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2006 q = 1) (hb : d361622 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d361622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2006, d361622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2007 q = 1) (hb : d361882 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2007, d361882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2007, d361882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100179 (p : Pattern) (ha : d2007 p = 1) (hb : d362098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d274587 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2005 q = 1) (hb : d362096 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d362096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, d362096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2006 q = 1) (hb : d362097 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d362097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2006, d362097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2007 q = 1) (hb : d362098 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2007, d362098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2007, d362098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100180 (p : Pattern) (ha : d34786 p = 1) (hb : d362104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d274587 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2005 q = 1) (hb : d362096 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d362096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, d362096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2006 q = 1) (hb : d362097 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d362097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2006, d362097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1531 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1547 q = 1) (hb : d361192 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d361192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1547, d361192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34786 q = 1) (hb : d362104 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d34786, d362104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34786, d362104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100181 (p : Pattern) (ha : d42936 p = 1) (hb : d361616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273807 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34366 q = 1) (hb : d361302 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34366, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42935 q = 1) (hb : d361615 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42935, d361615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42935, d361615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42936 q = 1) (hb : d361616 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42936, d361616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42936, d361616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100182 (p : Pattern) (ha : d43852 p = 1) (hb : d361429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d274587 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d361427 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d361427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d361427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d273807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34366 q = 1) (hb : d361302 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34366, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42591 q = 1) (hb : d361428 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42591, d361428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42591, d361428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1523 q = 1) (hb : d273807 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d42592 q = 1) (hb : d361302 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42592, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d1531 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43851 q = 1) (hb : d361303 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d43851, d361303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43851, d361303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43852 q = 1) (hb : d361429 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43852, d361429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43852, d361429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro100183 (p : Pattern) (ha : d43856 p = 1) (hb : d361304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1523 q = 1) (hb : d273807 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d42592 q = 1) (hb : d361302 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42592, d361302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1531 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d43851 q = 1) (hb : d361303 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d43851, d361303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43851, d361303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1547 q = 1) (hb : d361192 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d361192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1547, d361192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d43856 q = 1) (hb : d361304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43856, d361304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43856, d361304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100184 (p : Pattern) (ha : d43862 p = 1) (hb : d362110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h2 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43845 q = 1) (hb : d362101 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43845, d362101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43845, d362101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361881 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d43846 q = 1) (hb : d361883 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100178 q ha hb
    | true =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43847 q = 1) (hb : d361884 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43848 q = 1) (hb : d361885 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43849 q = 1) (hb : d362102 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43849, d362102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43849, d362102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d43850 q = 1) (hb : d362103 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43850, d362103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43850, d362103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43853 q = 1) (hb : d362105 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q ha hb
    | true =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100180 q ha hb
  have h11 (q : Pattern) (ha : d43854 q = 1) (hb : d362106 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43855 q = 1) (hb : d362107 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43855, d362107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43855, d362107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43859 q = 1) (hb : d361888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43859, d361888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43859, d361888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d43860 q = 1) (hb : d362108 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43860, d362108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43860, d362108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43861 q = 1) (hb : d362109 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43861, d362109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43861, d362109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43862 q = 1) (hb : d362110 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43862, d362110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43862, d362110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100185 (p : Pattern) (ha : d43867 p = 1) (hb : d361623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d274587 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d361427 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d361427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d361427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d361620 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2002 q = 1) (hb : d361621 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, d361621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, d361621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1523 q = 1) (hb : d273807 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1523, d273807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d2005 q = 1) (hb : d361620 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d361620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2005, d361620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2006 q = 1) (hb : d361622 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d361622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2006, d361622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43867 q = 1) (hb : d361623 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43867, d361623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43867, d361623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro100186 (p : Pattern) (ha : d43874 p = 1) (hb : d361899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d274587 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d274587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d361427 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d361427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d361427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34366 q = 1) (hb : d361896 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, d361896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34366, d361896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42591 q = 1) (hb : d361897 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42591, d361897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42591, d361897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1531 q = 1) (hb : d361191 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1531, d361191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43873 q = 1) (hb : d361898 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d43873, d361898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43873, d361898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43874 q = 1) (hb : d361899 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43874, d361899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43874, d361899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100187 (p : Pattern) (ha : d362123 p = 1) (hb : d363327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43853 q = 1) (hb : d362105 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q ha hb
    | true =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100180 q ha hb
  have h4 (q : Pattern) (ha : d43854 q = 1) (hb : d362106 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43855 q = 1) (hb : d362107 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43855, d362107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43855, d362107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43868 q = 1) (hb : d361624 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100185 q ha hb
    | true =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43869 q = 1) (hb : d361625 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d43870 q = 1) (hb : d361626 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43871 q = 1) (hb : d362115 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43871, d362115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43871, d362115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43872 q = 1) (hb : d362116 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43872, d362116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43872, d362116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d44016 q = 1) (hb : d362118 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44016, d362118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d44016, d362118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99998 q ha hb
  have h14 (q : Pattern) (ha : d44017 q = 1) (hb : d362119 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44017, d362119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44017, d362119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d362120 q = 1) (hb : d363324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d362120, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d362120, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h16 (q : Pattern) (ha : d362121 q = 1) (hb : d363325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d362121, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362121, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d362122 q = 1) (hb : d363326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d362122, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362122, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h18 (q : Pattern) (ha : d362123 q = 1) (hb : d363327 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d362123, d363327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d362123, d363327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100188 (p : Pattern) (ha : d362132 p = 1) (hb : d363333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43886 q = 1) (hb : d361900 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d43887 q = 1) (hb : d361901 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43888 q = 1) (hb : d362129 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43888, d362129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43888, d362129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43889 q = 1) (hb : d362130 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43889, d362130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43889, d362130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43890 q = 1) (hb : d362131 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43890, d362131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43890, d362131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d44016 q = 1) (hb : d362118 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44016, d362118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d44016, d362118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99998 q ha hb
  have h9 (q : Pattern) (ha : d44017 q = 1) (hb : d362119 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44017, d362119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44017, d362119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d362120 q = 1) (hb : d363324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d362120, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d362120, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d362121 q = 1) (hb : d363325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d362121, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362121, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d362122 q = 1) (hb : d363326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d362122, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362122, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d362132 q = 1) (hb : d363333 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d362132, d363333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d362132, d363333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100189 (p : Pattern) (ha : d362146 p = 1) (hb : d363341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d43853 q = 1) (hb : d362105 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q ha hb
    | true =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100180 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43854 q = 1) (hb : d362106 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d362137 q = 1) (hb : d363338 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d362137, d363338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362137, d363338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d43899 q = 1) (hb : d362138 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43899, d362138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43899, d362138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d362139 q = 1) (hb : d363339 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d362139, d363339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362139, d363339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d362140 q = 1) (hb : d363340 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d362140, d363340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362140, d363340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d5128 q = 1) (hb : d362141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h10 (q : Pattern) (ha : d5129 q = 1) (hb : d362142 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d362142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5129, d362142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d5130 q = 1) (hb : d362143 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d362143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5130, d362143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d5131 q = 1) (hb : d362144 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d362144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5131, d362144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5132 q = 1) (hb : d362145 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d362145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5132, d362145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d362146 q = 1) (hb : d363341 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d362146, d363341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362146, d363341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro100190 (p : Pattern) (ha : d362152 p = 1) (hb : d363347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43863 q = 1) (hb : d362111 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43863, d362111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100184 q ha hb
    | true =>
      simp only [d43863, d362111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43864 q = 1) (hb : d362112 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43864, d362112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43864, d362112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43865 q = 1) (hb : d362113 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43865, d362113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43865, d362113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43866 q = 1) (hb : d362114 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43866, d362114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43866, d362114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d362124 q = 1) (hb : d363328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362124, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100187 q ha hb
    | true =>
      simp only [d362124, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362125 q = 1) (hb : d363329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362125, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362125, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362126 q = 1) (hb : d363330 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362126, d363330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362126, d363330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362127 q = 1) (hb : d363331 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362127, d363331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362127, d363331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362128 q = 1) (hb : d363332 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362128, d363332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d362128, d363332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362133 q = 1) (hb : d363334 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100188 q ha hb
    | true =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362134 q = 1) (hb : d363335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d362135 q = 1) (hb : d363336 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362135, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362135, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362136 q = 1) (hb : d363337 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362136, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362136, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d362147 q = 1) (hb : d363342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
    | true =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362148 q = 1) (hb : d363343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d362149 q = 1) (hb : d363344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362149, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362149, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362150 q = 1) (hb : d363345 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362150, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362150, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d362151 q = 1) (hb : d363346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362151, d363346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362151, d363346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d362152 q = 1) (hb : d363347 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362152, d363347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362152, d363347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100191 (p : Pattern) (ha : d362158 p = 1) (hb : d363351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43853 q = 1) (hb : d362105 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q ha hb
    | true =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100180 q ha hb
  have h4 (q : Pattern) (ha : d43854 q = 1) (hb : d362106 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43855 q = 1) (hb : d362107 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43855, d362107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43855, d362107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43868 q = 1) (hb : d361624 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100185 q ha hb
    | true =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43869 q = 1) (hb : d361625 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d43870 q = 1) (hb : d361626 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43871 q = 1) (hb : d362115 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43871, d362115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43871, d362115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43872 q = 1) (hb : d362116 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43872, d362116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43872, d362116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d43909 q = 1) (hb : d362153 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43909, d362153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43909, d362153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h14 (q : Pattern) (ha : d43910 q = 1) (hb : d362154 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43910, d362154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43910, d362154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d362155 q = 1) (hb : d363348 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d362155, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d362155, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d362156 q = 1) (hb : d363349 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d362156, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362156, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d362157 q = 1) (hb : d363350 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d362157, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362157, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d362158 q = 1) (hb : d363351 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d362158, d363351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d362158, d363351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100192 (p : Pattern) (ha : d362163 p = 1) (hb : d363356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d43853 q = 1) (hb : d362105 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q ha hb
    | true =>
      simp only [d43853, d362105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100180 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43854 q = 1) (hb : d362106 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43854, d362106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43909 q = 1) (hb : d362153 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43909, d362153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43909, d362153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h4 (q : Pattern) (ha : d43910 q = 1) (hb : d362154 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43910, d362154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43910, d362154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d362155 q = 1) (hb : d363348 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d362155, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362155, d363348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362156 q = 1) (hb : d363349 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d362156, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362156, d363349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d362157 q = 1) (hb : d363350 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d362157, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362157, d363350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d5128 q = 1) (hb : d362141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h14 (q : Pattern) (ha : d5129 q = 1) (hb : d362142 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d362142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5129, d362142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d5130 q = 1) (hb : d362143 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d362143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5130, d362143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d5131 q = 1) (hb : d362144 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d362144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5131, d362144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5132 q = 1) (hb : d362145 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d362145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5132, d362145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d362163 q = 1) (hb : d363356 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d362163, d363356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362163, d363356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro100193 (p : Pattern) (ha : d362170 p = 1) (hb : d363363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362159 q = 1) (hb : d363352 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362159, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100191 q ha hb
    | true =>
      simp only [d362159, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362160 q = 1) (hb : d363353 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362160, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362160, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362161 q = 1) (hb : d363354 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362161, d363354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362161, d363354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362162 q = 1) (hb : d363355 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362162, d363355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362162, d363355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362164 q = 1) (hb : d363357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
    | true =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362165 q = 1) (hb : d363358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362166 q = 1) (hb : d363359 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362166, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362166, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362167 q = 1) (hb : d363360 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362167, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362167, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362168 q = 1) (hb : d363361 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362168, d363361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362168, d363361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362147 q = 1) (hb : d363342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
    | true =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362148 q = 1) (hb : d363343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d362149 q = 1) (hb : d363344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362149, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362149, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362150 q = 1) (hb : d363345 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362150, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362150, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d362169 q = 1) (hb : d363362 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362169, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362169, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362170 q = 1) (hb : d363363 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362170, d363363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362170, d363363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100194 (p : Pattern) (ha : d270160 p = 1) (hb : d362178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5128 q = 1) (hb : d362141 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5128, d362141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
  have h2 (q : Pattern) (ha : d5129 q = 1) (hb : d362142 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d362142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5129, d362142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26754 q = 1) (hb : d362175 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26754, d362175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26754, d362175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26755 q = 1) (hb : d362176 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26755, d362176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26755, d362176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26756 q = 1) (hb : d362177 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26756, d362177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26756, d362177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270160 q = 1) (hb : d362178 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d270160, d362178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270160, d362178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro100195 (p : Pattern) (ha : d362184 p = 1) (hb : d363368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362164 q = 1) (hb : d363357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
    | true =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362165 q = 1) (hb : d363358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362166 q = 1) (hb : d363359 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362166, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362166, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362167 q = 1) (hb : d363360 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362167, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362167, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362174 q = 1) (hb : d363367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362174, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362174, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d270161 q = 1) (hb : d362179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d270161, d362179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100194 q ha hb
    | true =>
      simp only [d270161, d362179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270162 q = 1) (hb : d362180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d270162, d362180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270162, d362180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270163 q = 1) (hb : d362181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d270163, d362181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270163, d362181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270164 q = 1) (hb : d362182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d270164, d362182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270164, d362182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d270165 q = 1) (hb : d362183 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d270165, d362183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270165, d362183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d362184 q = 1) (hb : d363368 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362184, d363368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362184, d363368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100196 (p : Pattern) (ha : d362191 p = 1) (hb : d363375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362171 q = 1) (hb : d363364 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362171, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100190 q ha hb
    | true =>
      simp only [d362171, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
  have h2 (q : Pattern) (ha : d362172 q = 1) (hb : d363365 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362172, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362172, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362173 q = 1) (hb : d363366 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362173, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362173, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362185 q = 1) (hb : d363369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
    | true =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100195 q ha hb
  have h5 (q : Pattern) (ha : d362186 q = 1) (hb : d363370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362187 q = 1) (hb : d363371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362188 q = 1) (hb : d363372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362188, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362188, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362189 q = 1) (hb : d363373 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362189, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362189, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362190 q = 1) (hb : d363374 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362190, d363374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362190, d363374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362191 q = 1) (hb : d363375 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362191, d363375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362191, d363375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100197 (p : Pattern) (ha : d362195 p = 1) (hb : d363379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362185 q = 1) (hb : d363369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
    | true =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100195 q ha hb
  have h2 (q : Pattern) (ha : d362186 q = 1) (hb : d363370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362187 q = 1) (hb : d363371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362189 q = 1) (hb : d363373 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362189, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362189, d363373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362194 q = 1) (hb : d363378 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362194, d363378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362194, d363378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362195 q = 1) (hb : d363379 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362195, d363379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362195, d363379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100198 (p : Pattern) (ha : d362201 p = 1) (hb : d363385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362198 q = 1) (hb : d363382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362199 q = 1) (hb : d363383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362200 q = 1) (hb : d363384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362200, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362200, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362201 q = 1) (hb : d363385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362201, d363385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362201, d363385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100199 (p : Pattern) (ha : d362205 p = 1) (hb : d363389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362202 q = 1) (hb : d363386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362203 q = 1) (hb : d363387 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362204 q = 1) (hb : d363388 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362204, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362204, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362205 q = 1) (hb : d363389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362205, d363389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362205, d363389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100200 (p : Pattern) (ha : d362211 p = 1) (hb : d363395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362206 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
    | true =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
  have h2 (q : Pattern) (ha : d362207 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362207, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362207, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362208 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362208, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362208, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362209 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362209, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362209, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362210 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362210, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362210, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362211 q = 1) (hb : d363395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362211, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362211, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100201 (p : Pattern) (ha : d362214 p = 1) (hb : d363398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362198 q = 1) (hb : d363382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362199 q = 1) (hb : d363383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362200 q = 1) (hb : d363384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362200, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362200, d363384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362214 q = 1) (hb : d363398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362214, d363398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362214, d363398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100202 (p : Pattern) (ha : d362215 p = 1) (hb : d363399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362202 q = 1) (hb : d363386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362203 q = 1) (hb : d363387 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362204 q = 1) (hb : d363388 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362204, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362204, d363388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362215 q = 1) (hb : d363399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362215, d363399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362215, d363399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100203 (p : Pattern) (ha : d362221 p = 1) (hb : d363405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362206 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
    | true =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
  have h2 (q : Pattern) (ha : d362207 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362207, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362207, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362208 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362208, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362208, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362209 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362209, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362209, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362210 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362210, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362210, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362216 q = 1) (hb : d363400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362216, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100201 q ha hb
    | true =>
      simp only [d362216, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100202 q ha hb
  have h7 (q : Pattern) (ha : d362217 q = 1) (hb : d363401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362217, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362217, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362218 q = 1) (hb : d363402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362218, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362218, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362219 q = 1) (hb : d363403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362219, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362219, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362220 q = 1) (hb : d363404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362220, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362220, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362221 q = 1) (hb : d363405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362221, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362221, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100204 (p : Pattern) (ha : d362226 p = 1) (hb : d363410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362198 q = 1) (hb : d363382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362199 q = 1) (hb : d363383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362225 q = 1) (hb : d363409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362225, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362225, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362226 q = 1) (hb : d363410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362226, d363410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362226, d363410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100205 (p : Pattern) (ha : d362228 p = 1) (hb : d363412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362202 q = 1) (hb : d363386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362203 q = 1) (hb : d363387 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362227 q = 1) (hb : d363411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362227, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362227, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362228 q = 1) (hb : d363412 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362228, d363412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362228, d363412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100206 (p : Pattern) (ha : d362235 p = 1) (hb : d363419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362198 q = 1) (hb : d363382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362233 q = 1) (hb : d363417 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362233, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362233, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362234 q = 1) (hb : d363418 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362234, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362234, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362235 q = 1) (hb : d363419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362235, d363419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362235, d363419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100207 (p : Pattern) (ha : d362238 p = 1) (hb : d363422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362202 q = 1) (hb : d363386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362236 q = 1) (hb : d363420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362236, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362236, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362237 q = 1) (hb : d363421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362237, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362237, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362238 q = 1) (hb : d363422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362238, d363422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362238, d363422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100208 (p : Pattern) (ha : d43990 p = 1) (hb : d362245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362244 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h3 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d43845 q = 1) (hb : d362101 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43845, d362101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43845, d362101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d361881 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d43846 q = 1) (hb : d361883 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100178 q ha hb
    | true =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43847 q = 1) (hb : d361884 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d43848 q = 1) (hb : d361885 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d43849 q = 1) (hb : d362102 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43849, d362102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43849, d362102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43850 q = 1) (hb : d362103 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43850, d362103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43850, d362103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d43990 q = 1) (hb : d362245 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43990, d362245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43990, d362245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100209 (p : Pattern) (ha : d42936 p = 1) (hb : d362251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d271326 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d271326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1519 q = 1) (hb : d273695 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d273695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34366 q = 1) (hb : d361896 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, d361896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34366, d361896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42935 q = 1) (hb : d362250 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42935, d362250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42935, d362250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42936 q = 1) (hb : d362251 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42936, d362251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42936, d362251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100210 (p : Pattern) (ha : d43998 p = 1) (hb : d362257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h2 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43845 q = 1) (hb : d362101 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43845, d362101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43845, d362101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361881 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d43846 q = 1) (hb : d361883 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100178 q ha hb
    | true =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43847 q = 1) (hb : d361884 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43848 q = 1) (hb : d361885 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43849 q = 1) (hb : d362102 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43849, d362102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43849, d362102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d43850 q = 1) (hb : d362103 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43850, d362103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43850, d362103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42937 q = 1) (hb : d362252 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, d362252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100209 q ha hb
    | true =>
      simp only [d42937, d362252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42938 q = 1) (hb : d362253 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, d362253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42938, d362253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43886 q = 1) (hb : d361900 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43887 q = 1) (hb : d361901 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43995 q = 1) (hb : d362254 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43995, d362254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43995, d362254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43996 q = 1) (hb : d362255 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43996, d362255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43996, d362255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43997 q = 1) (hb : d362256 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43997, d362256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43997, d362256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d43998 q = 1) (hb : d362257 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43998, d362257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43998, d362257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro100211 (p : Pattern) (ha : d44006 p = 1) (hb : d362266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d362252 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, d362252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100209 q ha hb
    | true =>
      simp only [d42937, d362252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d362253 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, d362253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, d362253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43405 q = 1) (hb : d362263 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43405, d362263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43405, d362263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44004 q = 1) (hb : d362264 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44004, d362264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44004, d362264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44005 q = 1) (hb : d362265 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44005, d362265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44005, d362265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43886 q = 1) (hb : d361900 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43887 q = 1) (hb : d361901 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43995 q = 1) (hb : d362254 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43995, d362254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43995, d362254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d43996 q = 1) (hb : d362255 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43996, d362255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43996, d362255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43997 q = 1) (hb : d362256 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43997, d362256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43997, d362256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44006 q = 1) (hb : d362266 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44006, d362266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44006, d362266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100212 (p : Pattern) (ha : d362272 p = 1) (hb : d363427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43991 q = 1) (hb : d362246 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43991, d362246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100208 q ha hb
    | true =>
      simp only [d43991, d362246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43992 q = 1) (hb : d362247 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43992, d362247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43992, d362247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43993 q = 1) (hb : d362248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43993, d362248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43993, d362248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43994 q = 1) (hb : d362249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43994, d362249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43994, d362249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43999 q = 1) (hb : d362258 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43999, d362258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100210 q ha hb
    | true =>
      simp only [d43999, d362258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44000 q = 1) (hb : d362259 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44000, d362259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44000, d362259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44001 q = 1) (hb : d362260 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44001, d362260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44001, d362260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44002 q = 1) (hb : d362261 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44002, d362261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44002, d362261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44003 q = 1) (hb : d362262 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44003, d362262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44003, d362262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44007 q = 1) (hb : d362267 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44007, d362267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100211 q ha hb
    | true =>
      simp only [d44007, d362267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44008 q = 1) (hb : d362268 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44008, d362268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44008, d362268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44009 q = 1) (hb : d362269 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44009, d362269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44009, d362269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44010 q = 1) (hb : d362270 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44010, d362270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44010, d362270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d362133 q = 1) (hb : d363334 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100188 q ha hb
    | true =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362134 q = 1) (hb : d363335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d362135 q = 1) (hb : d363336 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362135, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362135, d363336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362136 q = 1) (hb : d363337 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362136, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362136, d363337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d362271 q = 1) (hb : d363426 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362271, d363426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d362271, d363426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d362272 q = 1) (hb : d363427 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362272, d363427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d362272, d363427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100213 (p : Pattern) (ha : d362279 p = 1) (hb : d363431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d43843 q = 1) (hb : d362099 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d43843, d362099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100179 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43844 q = 1) (hb : d362100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43844, d362100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44016 q = 1) (hb : d362118 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44016, d362118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d44016, d362118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99998 q ha hb
  have h4 (q : Pattern) (ha : d44017 q = 1) (hb : d362119 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44017, d362119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44017, d362119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d44018 q = 1) (hb : d362276 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44018, d362276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44018, d362276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44019 q = 1) (hb : d362277 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44019, d362277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44019, d362277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d44020 q = 1) (hb : d362278 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44020, d362278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44020, d362278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d362120 q = 1) (hb : d363324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d362120, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d362120, d363324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d362121 q = 1) (hb : d363325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d362121, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362121, d363325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d362122 q = 1) (hb : d363326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d362122, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362122, d363326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d362279 q = 1) (hb : d363431 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d362279, d363431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d362279, d363431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100214 (p : Pattern) (ha : d362285 p = 1) (hb : d363437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362280 q = 1) (hb : d363432 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362280, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100213 q ha hb
    | true =>
      simp only [d362280, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362281 q = 1) (hb : d363433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362281, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362281, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362282 q = 1) (hb : d363434 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362282, d363434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362282, d363434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362283 q = 1) (hb : d363435 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362283, d363435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362283, d363435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362147 q = 1) (hb : d363342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
    | true =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362148 q = 1) (hb : d363343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362149 q = 1) (hb : d363344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362149, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362149, d363344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362150 q = 1) (hb : d363345 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362150, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362150, d363345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362284 q = 1) (hb : d363436 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362284, d363436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362284, d363436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362169 q = 1) (hb : d363362 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362169, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362169, d363362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362285 q = 1) (hb : d363437 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362285, d363437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362285, d363437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100215 (p : Pattern) (ha : d362291 p = 1) (hb : d363443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362273 q = 1) (hb : d363428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362273, d363428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100212 q ha hb
    | true =>
      simp only [d362273, d363428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100190 q ha hb
  have h2 (q : Pattern) (ha : d362274 q = 1) (hb : d363429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362274, d363429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362274, d363429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362275 q = 1) (hb : d363430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362275, d363430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362275, d363430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362286 q = 1) (hb : d363438 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362286, d363438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100190 q ha hb
    | true =>
      simp only [d362286, d363438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100214 q ha hb
  have h5 (q : Pattern) (ha : d362287 q = 1) (hb : d363439 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362287, d363439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362287, d363439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362288 q = 1) (hb : d363440 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362288, d363440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362288, d363440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362289 q = 1) (hb : d363441 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362289, d363441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362289, d363441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362171 q = 1) (hb : d363364 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362171, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100190 q ha hb
    | true =>
      simp only [d362171, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
  have h9 (q : Pattern) (ha : d362172 q = 1) (hb : d363365 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362172, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362172, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362173 q = 1) (hb : d363366 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362173, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362173, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362185 q = 1) (hb : d363369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
    | true =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100195 q ha hb
  have h12 (q : Pattern) (ha : d362186 q = 1) (hb : d363370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362187 q = 1) (hb : d363371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362188 q = 1) (hb : d363372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362188, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362188, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d362290 q = 1) (hb : d363442 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362290, d363442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362290, d363442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d362291 q = 1) (hb : d363443 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362291, d363443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362291, d363443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100216 (p : Pattern) (ha : d362297 p = 1) (hb : d363449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362292 q = 1) (hb : d363444 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362292, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100215 q ha hb
    | true =>
      simp only [d362292, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362293 q = 1) (hb : d363445 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362293, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362293, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362294 q = 1) (hb : d363446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362294, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362294, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362295 q = 1) (hb : d363447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362295, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362295, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362296 q = 1) (hb : d363448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362296, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362296, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362297 q = 1) (hb : d363449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362297, d363449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362297, d363449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100217 (p : Pattern) (ha : d362300 p = 1) (hb : d363452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362164 q = 1) (hb : d363357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
    | true =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362165 q = 1) (hb : d363358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362166 q = 1) (hb : d363359 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362166, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362166, d363359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362167 q = 1) (hb : d363360 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362167, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362167, d363360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362174 q = 1) (hb : d363367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362174, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362174, d363367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362300 q = 1) (hb : d363452 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362300, d363452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362300, d363452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100218 (p : Pattern) (ha : d362306 p = 1) (hb : d363458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362171 q = 1) (hb : d363364 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362171, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100190 q ha hb
    | true =>
      simp only [d362171, d363364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
  have h2 (q : Pattern) (ha : d362172 q = 1) (hb : d363365 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362172, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362172, d363365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362173 q = 1) (hb : d363366 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362173, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362173, d363366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362185 q = 1) (hb : d363369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
    | true =>
      simp only [d362185, d363369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100195 q ha hb
  have h5 (q : Pattern) (ha : d362186 q = 1) (hb : d363370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362186, d363370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362187 q = 1) (hb : d363371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362187, d363371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362188 q = 1) (hb : d363372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362188, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362188, d363372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362301 q = 1) (hb : d363453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362301, d363453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100193 q ha hb
    | true =>
      simp only [d362301, d363453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100217 q ha hb
  have h9 (q : Pattern) (ha : d362302 q = 1) (hb : d363454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362302, d363454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362302, d363454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362303 q = 1) (hb : d363455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362303, d363455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362303, d363455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362304 q = 1) (hb : d363456 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362304, d363456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362304, d363456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d362305 q = 1) (hb : d363457 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362305, d363457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362305, d363457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362306 q = 1) (hb : d363458 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362306, d363458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362306, d363458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100219 (p : Pattern) (ha : d362312 p = 1) (hb : d363464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362307 q = 1) (hb : d363459 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362307, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100218 q ha hb
    | true =>
      simp only [d362307, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362308 q = 1) (hb : d363460 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362308, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362308, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362309 q = 1) (hb : d363461 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362309, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362309, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362310 q = 1) (hb : d363462 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362310, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362310, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362311 q = 1) (hb : d363463 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362311, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362311, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362312 q = 1) (hb : d363464 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362312, d363464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362312, d363464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100220 (p : Pattern) (ha : d362318 p = 1) (hb : d363470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362229 q = 1) (hb : d363413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362229, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100204 q ha hb
    | true =>
      simp only [d362229, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100205 q ha hb
  have h2 (q : Pattern) (ha : d362230 q = 1) (hb : d363414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362230, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362230, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362231 q = 1) (hb : d363415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362231, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362231, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362232 q = 1) (hb : d363416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362232, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362232, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362239 q = 1) (hb : d363423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362239, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100206 q ha hb
    | true =>
      simp only [d362239, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100207 q ha hb
  have h6 (q : Pattern) (ha : d362240 q = 1) (hb : d363424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362240, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362240, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362241 q = 1) (hb : d363425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362241, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362241, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362298 q = 1) (hb : d363450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362298, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100216 q ha hb
    | true =>
      simp only [d362298, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d362206 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d362299 q = 1) (hb : d363451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362299, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362299, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d362313 q = 1) (hb : d363465 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362313, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100219 q ha hb
    | true =>
      simp only [d362313, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d362314 q = 1) (hb : d363466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362314, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362314, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362315 q = 1) (hb : d363467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362315, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362315, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362316 q = 1) (hb : d363468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362316, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362316, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d362317 q = 1) (hb : d363469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362317, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362317, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d362318 q = 1) (hb : d363470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362318, d363470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362318, d363470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100221 (p : Pattern) (ha : d362319 p = 1) (hb : d363471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362198 q = 1) (hb : d363382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362199 q = 1) (hb : d363383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362199, d363383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362225 q = 1) (hb : d363409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362225, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362225, d363409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362319 q = 1) (hb : d363471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362319, d363471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362319, d363471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100222 (p : Pattern) (ha : d362320 p = 1) (hb : d363472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362202 q = 1) (hb : d363386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362203 q = 1) (hb : d363387 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362203, d363387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362227 q = 1) (hb : d363411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362227, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362227, d363411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362320 q = 1) (hb : d363472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362320, d363472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362320, d363472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100223 (p : Pattern) (ha : d362325 p = 1) (hb : d363477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362198 q = 1) (hb : d363382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362198, d363382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362233 q = 1) (hb : d363417 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362233, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362233, d363417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362234 q = 1) (hb : d363418 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362234, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362234, d363418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362325 q = 1) (hb : d363477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362325, d363477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362325, d363477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100224 (p : Pattern) (ha : d362326 p = 1) (hb : d363478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362196 q = 1) (hb : d363380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100197 q ha hb
    | true =>
      simp only [d362196, d363380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362197 q = 1) (hb : d363381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362197, d363381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362202 q = 1) (hb : d363386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362202, d363386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362236 q = 1) (hb : d363420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362236, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362236, d363420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362237 q = 1) (hb : d363421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362237, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362237, d363421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362326 q = 1) (hb : d363478 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362326, d363478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362326, d363478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100225 (p : Pattern) (ha : d362330 p = 1) (hb : d363482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362292 q = 1) (hb : d363444 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362292, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100215 q ha hb
    | true =>
      simp only [d362292, d363444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362293 q = 1) (hb : d363445 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362293, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362293, d363445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362192 q = 1) (hb : d363376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100196 q ha hb
    | true =>
      simp only [d362192, d363376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362193 q = 1) (hb : d363377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362193, d363377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362294 q = 1) (hb : d363446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362294, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362294, d363446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362295 q = 1) (hb : d363447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362295, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362295, d363447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362296 q = 1) (hb : d363448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362296, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362296, d363448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362330 q = 1) (hb : d363482 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362330, d363482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362330, d363482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100226 (p : Pattern) (ha : d362333 p = 1) (hb : d363485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362307 q = 1) (hb : d363459 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362307, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100218 q ha hb
    | true =>
      simp only [d362307, d363459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362308 q = 1) (hb : d363460 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362308, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362308, d363460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362309 q = 1) (hb : d363461 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362309, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362309, d363461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362310 q = 1) (hb : d363462 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362310, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362310, d363462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362311 q = 1) (hb : d363463 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362311, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362311, d363463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362333 q = 1) (hb : d363485 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362333, d363485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362333, d363485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100227 (p : Pattern) (ha : d362339 p = 1) (hb : d363491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362229 q = 1) (hb : d363413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362229, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100204 q ha hb
    | true =>
      simp only [d362229, d363413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100205 q ha hb
  have h2 (q : Pattern) (ha : d362230 q = 1) (hb : d363414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362230, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362230, d363414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362231 q = 1) (hb : d363415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362231, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362231, d363415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362232 q = 1) (hb : d363416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362232, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362232, d363416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362239 q = 1) (hb : d363423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362239, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100206 q ha hb
    | true =>
      simp only [d362239, d363423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100207 q ha hb
  have h6 (q : Pattern) (ha : d362240 q = 1) (hb : d363424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362240, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362240, d363424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362241 q = 1) (hb : d363425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362241, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362241, d363425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362298 q = 1) (hb : d363450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362298, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100216 q ha hb
    | true =>
      simp only [d362298, d363450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d362206 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d362299 q = 1) (hb : d363451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362299, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362299, d363451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d362313 q = 1) (hb : d363465 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362313, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100219 q ha hb
    | true =>
      simp only [d362313, d363465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d362314 q = 1) (hb : d363466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362314, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362314, d363466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362315 q = 1) (hb : d363467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362315, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362315, d363467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362316 q = 1) (hb : d363468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362316, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362316, d363468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d362317 q = 1) (hb : d363469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362317, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362317, d363469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d362321 q = 1) (hb : d363473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362321, d363473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100221 q ha hb
    | true =>
      simp only [d362321, d363473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100222 q ha hb
  have h17 (q : Pattern) (ha : d362322 q = 1) (hb : d363474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362322, d363474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362322, d363474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d362323 q = 1) (hb : d363475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362323, d363475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d362323, d363475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d362324 q = 1) (hb : d363476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362324, d363476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362324, d363476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d362327 q = 1) (hb : d363479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362327, d363479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100223 q ha hb
    | true =>
      simp only [d362327, d363479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100224 q ha hb
  have h21 (q : Pattern) (ha : d362328 q = 1) (hb : d363480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362328, d363480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362328, d363480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d362329 q = 1) (hb : d363481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362329, d363481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d362329, d363481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d362331 q = 1) (hb : d363483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362331, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100225 q ha hb
    | true =>
      simp only [d362331, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100201 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d362216 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d362332 q = 1) (hb : d363484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362332, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d362332, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d362334 q = 1) (hb : d363486 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362334, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100226 q ha hb
    | true =>
      simp only [d362334, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d362335 q = 1) (hb : d363487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362335, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d362335, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d362336 q = 1) (hb : d363488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362336, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d362336, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d362337 q = 1) (hb : d363489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362337, d363489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d362337, d363489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d362338 q = 1) (hb : d363490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362338, d363490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362338, d363490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d362339 q = 1) (hb : d363491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362339, d363491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362339, d363491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro100228 (p : Pattern) (ha : d362346 p = 1) (hb : d363498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362206 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
    | true =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
  have h2 (q : Pattern) (ha : d362207 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362207, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362207, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362208 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362208, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362208, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362209 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362209, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362209, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362210 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362210, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362210, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362341 q = 1) (hb : d363493 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362341, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
    | true =>
      simp only [d362341, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362342 q = 1) (hb : d363494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362342, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362342, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362343 q = 1) (hb : d363495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362343, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362343, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362344 q = 1) (hb : d363496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362344, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362344, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362345 q = 1) (hb : d363497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362345, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362345, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362346 q = 1) (hb : d363498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362346, d363498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362346, d363498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100229 (p : Pattern) (ha : d362352 p = 1) (hb : d363504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362341 q = 1) (hb : d363493 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362341, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
    | true =>
      simp only [d362341, d363493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362342 q = 1) (hb : d363494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362342, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362342, d363494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362343 q = 1) (hb : d363495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362343, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362343, d363495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362344 q = 1) (hb : d363496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362344, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362344, d363496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362345 q = 1) (hb : d363497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362345, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362345, d363497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362347 q = 1) (hb : d363499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362347, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100202 q ha hb
    | true =>
      simp only [d362347, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362348 q = 1) (hb : d363500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362348, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362348, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362349 q = 1) (hb : d363501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362349, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362349, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362350 q = 1) (hb : d363502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362350, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362350, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362351 q = 1) (hb : d363503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362351, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362351, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362352 q = 1) (hb : d363504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362352, d363504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362352, d363504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100230 (p : Pattern) (ha : d362359 p = 1) (hb : d363511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362331 q = 1) (hb : d363483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362331, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100225 q ha hb
    | true =>
      simp only [d362331, d363483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100201 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362332 q = 1) (hb : d363484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362332, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362332, d363484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d362334 q = 1) (hb : d363486 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362334, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100226 q ha hb
    | true =>
      simp only [d362334, d363486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362335 q = 1) (hb : d363487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362335, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362335, d363487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362336 q = 1) (hb : d363488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362336, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362336, d363488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362357 q = 1) (hb : d363509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362357, d363509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362357, d363509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362358 q = 1) (hb : d363510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362358, d363510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362358, d363510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362359 q = 1) (hb : d363511 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362359, d363511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362359, d363511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100231 (p : Pattern) (ha : d362361 p = 1) (hb : d363513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362347 q = 1) (hb : d363499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362347, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100202 q ha hb
    | true =>
      simp only [d362347, d363499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362348 q = 1) (hb : d363500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362348, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362348, d363500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362349 q = 1) (hb : d363501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362349, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362349, d363501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362350 q = 1) (hb : d363502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362350, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362350, d363502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362351 q = 1) (hb : d363503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362351, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362351, d363503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362361 q = 1) (hb : d363513 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362361, d363513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362361, d363513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100232 (p : Pattern) (ha : d362385 p = 1) (hb : d363524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44237 q = 1) (hb : d362367 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44237, d362367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44237, d362367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100208 q ha hb
  have h2 (q : Pattern) (ha : d43991 q = 1) (hb : d362246 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43991, d362246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100208 q ha hb
    | true =>
      simp only [d43991, d362246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44238 q = 1) (hb : d362368 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44238, d362368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44238, d362368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43992 q = 1) (hb : d362247 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43992, d362247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43992, d362247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44239 q = 1) (hb : d362369 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44239, d362369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44239, d362369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44240 q = 1) (hb : d362370 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44240, d362370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44240, d362370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44241 q = 1) (hb : d362371 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44241, d362371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44241, d362371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100210 q ha hb
  have h8 (q : Pattern) (ha : d43999 q = 1) (hb : d362258 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43999, d362258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100210 q ha hb
    | true =>
      simp only [d43999, d362258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44242 q = 1) (hb : d362372 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44242, d362372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44242, d362372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44000 q = 1) (hb : d362259 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44000, d362259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44000, d362259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44243 q = 1) (hb : d362373 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44243, d362373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44243, d362373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44244 q = 1) (hb : d362374 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44244, d362374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44244, d362374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44245 q = 1) (hb : d362375 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44245, d362375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44245, d362375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44246 q = 1) (hb : d362376 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44246, d362376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44246, d362376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100211 q ha hb
  have h15 (q : Pattern) (ha : d44007 q = 1) (hb : d362267 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44007, d362267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100211 q ha hb
    | true =>
      simp only [d44007, d362267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44247 q = 1) (hb : d362377 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44247, d362377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44247, d362377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44008 q = 1) (hb : d362268 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44008, d362268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44008, d362268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d44248 q = 1) (hb : d362378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44248, d362378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44248, d362378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44249 q = 1) (hb : d362379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44249, d362379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44249, d362379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d362380 q = 1) (hb : d363519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362380, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362380, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100188 q ha hb
  have h21 (q : Pattern) (ha : d362133 q = 1) (hb : d363334 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100188 q ha hb
    | true =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d362381 q = 1) (hb : d363520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362381, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d362381, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d362134 q = 1) (hb : d363335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d362382 q = 1) (hb : d363521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362382, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d362382, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d362383 q = 1) (hb : d363522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362383, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d362383, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d362384 q = 1) (hb : d363523 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362384, d363523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d362384, d363523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d362385 q = 1) (hb : d363524 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362385, d363524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d362385, d363524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100233 (p : Pattern) (ha : d362400 p = 1) (hb : d363535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44256 q = 1) (hb : d362386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44256, d362386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44256, d362386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100184 q ha hb
  have h2 (q : Pattern) (ha : d43863 q = 1) (hb : d362111 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43863, d362111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100184 q ha hb
    | true =>
      simp only [d43863, d362111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44257 q = 1) (hb : d362387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44257, d362387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44257, d362387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43864 q = 1) (hb : d362112 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43864, d362112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43864, d362112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44258 q = 1) (hb : d362388 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44258, d362388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44258, d362388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44259 q = 1) (hb : d362389 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44259, d362389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44259, d362389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d362390 q = 1) (hb : d363525 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362390, d363525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362390, d363525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100187 q ha hb
  have h8 (q : Pattern) (ha : d362124 q = 1) (hb : d363328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362124, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100187 q ha hb
    | true =>
      simp only [d362124, d363328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362391 q = 1) (hb : d363526 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362391, d363526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362391, d363526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362125 q = 1) (hb : d363329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362125, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362125, d363329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362392 q = 1) (hb : d363527 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362392, d363527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362392, d363527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362393 q = 1) (hb : d363528 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362393, d363528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362393, d363528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362394 q = 1) (hb : d363529 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362394, d363529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d362394, d363529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362380 q = 1) (hb : d363519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362380, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362380, d363519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100188 q ha hb
  have h15 (q : Pattern) (ha : d362133 q = 1) (hb : d363334 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100188 q ha hb
    | true =>
      simp only [d362133, d363334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d362381 q = 1) (hb : d363520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362381, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362381, d363520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362134 q = 1) (hb : d363335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362134, d363335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d362382 q = 1) (hb : d363521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362382, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362382, d363521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d362383 q = 1) (hb : d363522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362383, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d362383, d363522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d362395 q = 1) (hb : d363530 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362395, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362395, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
  have h21 (q : Pattern) (ha : d362147 q = 1) (hb : d363342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
    | true =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d362396 q = 1) (hb : d363531 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362396, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d362396, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d362148 q = 1) (hb : d363343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d362397 q = 1) (hb : d363532 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362397, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d362397, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d362398 q = 1) (hb : d363533 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362398, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d362398, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d362399 q = 1) (hb : d363534 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362399, d363534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362399, d363534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d362400 q = 1) (hb : d363535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362400, d363535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362400, d363535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100234 (p : Pattern) (ha : d362410 p = 1) (hb : d363545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362404 q = 1) (hb : d363539 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362404, d363539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362404, d363539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100213 q ha hb
  have h2 (q : Pattern) (ha : d362280 q = 1) (hb : d363432 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362280, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100213 q ha hb
    | true =>
      simp only [d362280, d363432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362405 q = 1) (hb : d363540 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362405, d363540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362405, d363540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362281 q = 1) (hb : d363433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362281, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362281, d363433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362406 q = 1) (hb : d363541 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362406, d363541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362406, d363541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362407 q = 1) (hb : d363542 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362407, d363542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362407, d363542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362395 q = 1) (hb : d363530 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362395, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362395, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
  have h8 (q : Pattern) (ha : d362147 q = 1) (hb : d363342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
    | true =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362396 q = 1) (hb : d363531 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362396, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362396, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362148 q = 1) (hb : d363343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362397 q = 1) (hb : d363532 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362397, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362397, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362398 q = 1) (hb : d363533 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362398, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362398, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362408 q = 1) (hb : d363543 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362408, d363543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362408, d363543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362409 q = 1) (hb : d363544 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362409, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362409, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362410 q = 1) (hb : d363545 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362410, d363545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362410, d363545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100235 (p : Pattern) (ha : d362424 p = 1) (hb : d363559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362415 q = 1) (hb : d363550 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362415, d363550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362415, d363550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100191 q ha hb
  have h2 (q : Pattern) (ha : d362159 q = 1) (hb : d363352 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362159, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100191 q ha hb
    | true =>
      simp only [d362159, d363352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362416 q = 1) (hb : d363551 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362416, d363551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362416, d363551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362160 q = 1) (hb : d363353 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362160, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362160, d363353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362417 q = 1) (hb : d363552 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362417, d363552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362417, d363552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362418 q = 1) (hb : d363553 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362418, d363553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362418, d363553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362419 q = 1) (hb : d363554 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362419, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362419, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
  have h8 (q : Pattern) (ha : d362164 q = 1) (hb : d363357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
    | true =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362420 q = 1) (hb : d363555 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362420, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362420, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362165 q = 1) (hb : d363358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362421 q = 1) (hb : d363556 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362421, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362421, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362422 q = 1) (hb : d363557 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362422, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362422, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362423 q = 1) (hb : d363558 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362423, d363558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362423, d363558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362395 q = 1) (hb : d363530 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362395, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362395, d363530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
  have h15 (q : Pattern) (ha : d362147 q = 1) (hb : d363342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100189 q ha hb
    | true =>
      simp only [d362147, d363342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d362396 q = 1) (hb : d363531 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362396, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362396, d363531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362148 q = 1) (hb : d363343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362148, d363343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d362397 q = 1) (hb : d363532 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362397, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362397, d363532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d362398 q = 1) (hb : d363533 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362398, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d362398, d363533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d362409 q = 1) (hb : d363544 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362409, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362409, d363544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d362424 q = 1) (hb : d363559 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362424, d363559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362424, d363559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100236 (p : Pattern) (ha : d362434 p = 1) (hb : d363564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362419 q = 1) (hb : d363554 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362419, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362419, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
  have h2 (q : Pattern) (ha : d362164 q = 1) (hb : d363357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
    | true =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362420 q = 1) (hb : d363555 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362420, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362420, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362165 q = 1) (hb : d363358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362421 q = 1) (hb : d363556 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362421, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362421, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362422 q = 1) (hb : d363557 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362422, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362422, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362428 q = 1) (hb : d363563 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362428, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362428, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d270386 q = 1) (hb : d362429 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d270386, d362429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270386, d362429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100194 q ha hb
  have h9 (q : Pattern) (ha : d270161 q = 1) (hb : d362179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d270161, d362179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100194 q ha hb
    | true =>
      simp only [d270161, d362179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d270387 q = 1) (hb : d362430 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d270387, d362430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270387, d362430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d270162 q = 1) (hb : d362180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d270162, d362180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270162, d362180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270388 q = 1) (hb : d362431 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d270388, d362431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270388, d362431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270389 q = 1) (hb : d362432 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d270389, d362432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270389, d362432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270390 q = 1) (hb : d362433 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d270390, d362433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270390, d362433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d362434 q = 1) (hb : d363564 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362434, d363564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362434, d363564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro100237 (p : Pattern) (ha : d362440 p = 1) (hb : d363570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362401 q = 1) (hb : d363536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362401, d363536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100232 q ha hb
    | true =>
      simp only [d362401, d363536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100233 q ha hb
  have h2 (q : Pattern) (ha : d362402 q = 1) (hb : d363537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362402, d363537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362402, d363537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362403 q = 1) (hb : d363538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362403, d363538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362403, d363538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362411 q = 1) (hb : d363546 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362411, d363546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100233 q ha hb
    | true =>
      simp only [d362411, d363546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100234 q ha hb
  have h5 (q : Pattern) (ha : d362412 q = 1) (hb : d363547 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362412, d363547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362412, d363547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362413 q = 1) (hb : d363548 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362413, d363548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362413, d363548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362414 q = 1) (hb : d363549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362414, d363549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362414, d363549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362425 q = 1) (hb : d363560 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362425, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100233 q ha hb
    | true =>
      simp only [d362425, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
  have h9 (q : Pattern) (ha : d362426 q = 1) (hb : d363561 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362426, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362426, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362427 q = 1) (hb : d363562 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362427, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362427, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362435 q = 1) (hb : d363565 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
    | true =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100236 q ha hb
  have h12 (q : Pattern) (ha : d362436 q = 1) (hb : d363566 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362437 q = 1) (hb : d363567 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362438 q = 1) (hb : d363568 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362438, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362438, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d362439 q = 1) (hb : d363569 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362439, d363569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362439, d363569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d362440 q = 1) (hb : d363570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362440, d363570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362440, d363570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100238 (p : Pattern) (ha : d362445 p = 1) (hb : d363575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362425 q = 1) (hb : d363560 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362425, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100233 q ha hb
    | true =>
      simp only [d362425, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
  have h2 (q : Pattern) (ha : d362426 q = 1) (hb : d363561 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362426, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362426, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362427 q = 1) (hb : d363562 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362427, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362427, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362435 q = 1) (hb : d363565 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
    | true =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100236 q ha hb
  have h5 (q : Pattern) (ha : d362436 q = 1) (hb : d363566 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362437 q = 1) (hb : d363567 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362438 q = 1) (hb : d363568 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362438, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362438, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362443 q = 1) (hb : d363573 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362443, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362443, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362444 q = 1) (hb : d363574 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362444, d363574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362444, d363574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362445 q = 1) (hb : d363575 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362445, d363575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362445, d363575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100239 (p : Pattern) (ha : d362451 p = 1) (hb : d363581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362441 q = 1) (hb : d363571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362441, d363571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100237 q ha hb
    | true =>
      simp only [d362441, d363571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362442 q = 1) (hb : d363572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362442, d363572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362442, d363572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362446 q = 1) (hb : d363576 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362446, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100238 q ha hb
    | true =>
      simp only [d362446, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362447 q = 1) (hb : d363577 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362447, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362447, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362448 q = 1) (hb : d363578 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362448, d363578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362448, d363578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362449 q = 1) (hb : d363579 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362449, d363579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362449, d363579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362450 q = 1) (hb : d363580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362450, d363580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362450, d363580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362451 q = 1) (hb : d363581 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362451, d363581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362451, d363581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100240 (p : Pattern) (ha : d362453 p = 1) (hb : d363583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362435 q = 1) (hb : d363565 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
    | true =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100236 q ha hb
  have h2 (q : Pattern) (ha : d362436 q = 1) (hb : d363566 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362437 q = 1) (hb : d363567 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362443 q = 1) (hb : d363573 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362443, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362443, d363573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362452 q = 1) (hb : d363582 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362452, d363582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362452, d363582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362453 q = 1) (hb : d363583 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362453, d363583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362453, d363583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100241 (p : Pattern) (ha : d362459 p = 1) (hb : d363589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362446 q = 1) (hb : d363576 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362446, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100238 q ha hb
    | true =>
      simp only [d362446, d363576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362447 q = 1) (hb : d363577 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362447, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362447, d363577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362454 q = 1) (hb : d363584 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362454, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100240 q ha hb
    | true =>
      simp only [d362454, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362455 q = 1) (hb : d363585 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362455, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362455, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362456 q = 1) (hb : d363586 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362456, d363586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362456, d363586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362457 q = 1) (hb : d363587 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362457, d363587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362457, d363587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362458 q = 1) (hb : d363588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362458, d363588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362458, d363588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362459 q = 1) (hb : d363589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362459, d363589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362459, d363589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100242 (p : Pattern) (ha : d362467 p = 1) (hb : d363592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362419 q = 1) (hb : d363554 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362419, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362419, d363554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
  have h2 (q : Pattern) (ha : d362164 q = 1) (hb : d363357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100192 q ha hb
    | true =>
      simp only [d362164, d363357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362420 q = 1) (hb : d363555 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362420, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362420, d363555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362165 q = 1) (hb : d363358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362165, d363358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362421 q = 1) (hb : d363556 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362421, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362421, d363556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362422 q = 1) (hb : d363557 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362422, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362422, d363557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362428 q = 1) (hb : d363563 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362428, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362428, d363563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362467 q = 1) (hb : d363592 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362467, d363592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362467, d363592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100243 (p : Pattern) (ha : d362473 p = 1) (hb : d363598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362425 q = 1) (hb : d363560 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362425, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100233 q ha hb
    | true =>
      simp only [d362425, d363560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
  have h2 (q : Pattern) (ha : d362426 q = 1) (hb : d363561 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362426, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362426, d363561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362427 q = 1) (hb : d363562 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362427, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362427, d363562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362435 q = 1) (hb : d363565 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
    | true =>
      simp only [d362435, d363565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100236 q ha hb
  have h5 (q : Pattern) (ha : d362436 q = 1) (hb : d363566 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362436, d363566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362437 q = 1) (hb : d363567 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362437, d363567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362438 q = 1) (hb : d363568 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362438, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362438, d363568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362468 q = 1) (hb : d363593 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362468, d363593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100235 q ha hb
    | true =>
      simp only [d362468, d363593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100242 q ha hb
  have h9 (q : Pattern) (ha : d362469 q = 1) (hb : d363594 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362469, d363594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362469, d363594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362470 q = 1) (hb : d363595 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362470, d363595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362470, d363595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362471 q = 1) (hb : d363596 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362471, d363596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362471, d363596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d362472 q = 1) (hb : d363597 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362472, d363597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362472, d363597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362473 q = 1) (hb : d363598 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362473, d363598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362473, d363598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100244 (p : Pattern) (ha : d362479 p = 1) (hb : d363604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362474 q = 1) (hb : d363599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362474, d363599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100243 q ha hb
    | true =>
      simp only [d362474, d363599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362475 q = 1) (hb : d363600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362475, d363600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362475, d363600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362476 q = 1) (hb : d363601 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362476, d363601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362476, d363601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362477 q = 1) (hb : d363602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362477, d363602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362477, d363602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362478 q = 1) (hb : d363603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362478, d363603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362478, d363603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362479 q = 1) (hb : d363604 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362479, d363604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362479, d363604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100245 (p : Pattern) (ha : d362485 p = 1) (hb : d363610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362460 q = 1) (hb : d363590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362460, d363590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100239 q ha hb
    | true =>
      simp only [d362460, d363590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100241 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362465 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362466 q = 1) (hb : d363591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362466, d363591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362466, d363591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d362480 q = 1) (hb : d363605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362480, d363605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100244 q ha hb
    | true =>
      simp only [d362480, d363605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362481 q = 1) (hb : d363606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362481, d363606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362481, d363606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362482 q = 1) (hb : d363607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362482, d363607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362482, d363607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362483 q = 1) (hb : d363608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362483, d363608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362483, d363608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362484 q = 1) (hb : d363609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362484, d363609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362484, d363609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362485 q = 1) (hb : d363610 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362485, d363610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362485, d363610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100246 (p : Pattern) (ha : d362464 p = 1) (hb : d363615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362454 q = 1) (hb : d363584 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362454, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100240 q ha hb
    | true =>
      simp only [d362454, d363584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362455 q = 1) (hb : d363585 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362455, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362455, d363585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362461 q = 1) (hb : d363612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362461, d363612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362461, d363612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362462 q = 1) (hb : d363613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362462, d363613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362462, d363613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362463 q = 1) (hb : d363614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362463, d363614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362463, d363614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362464 q = 1) (hb : d363615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362464, d363615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362464, d363615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100247 (p : Pattern) (ha : d362492 p = 1) (hb : d363621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362487 q = 1) (hb : d363616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362487, d363616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100246 q ha hb
    | true =>
      simp only [d362487, d363616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362488 q = 1) (hb : d363617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362488, d363617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362488, d363617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362489 q = 1) (hb : d363618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362489, d363618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362489, d363618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362490 q = 1) (hb : d363619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362490, d363619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362490, d363619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362491 q = 1) (hb : d363620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362491, d363620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362491, d363620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362492 q = 1) (hb : d363621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362492, d363621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362492, d363621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100248 (p : Pattern) (ha : d362498 p = 1) (hb : d363627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362212 q = 1) (hb : d363396 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362212, d363396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362212, d363396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100200 q ha hb
  have h2 (q : Pattern) (ha : d362213 q = 1) (hb : d363397 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362213, d363397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362213, d363397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362222 q = 1) (hb : d363406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362222, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100200 q ha hb
    | true =>
      simp only [d362222, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100203 q ha hb
  have h4 (q : Pattern) (ha : d362223 q = 1) (hb : d363407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362223, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362223, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362224 q = 1) (hb : d363408 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362224, d363408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362224, d363408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362340 q = 1) (hb : d363492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362340, d363492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100220 q ha hb
    | true =>
      simp only [d362340, d363492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100227 q ha hb
  have h7 (q : Pattern) (ha : d362353 q = 1) (hb : d363505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362353, d363505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100228 q ha hb
    | true =>
      simp only [d362353, d363505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100229 q ha hb
  have h8 (q : Pattern) (ha : d362354 q = 1) (hb : d363506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362354, d363506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362354, d363506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362355 q = 1) (hb : d363507 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362355, d363507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362355, d363507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d362356 q = 1) (hb : d363508 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362356, d363508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362356, d363508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362360 q = 1) (hb : d363512 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362360, d363512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362360, d363512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100230 q ha hb
  have h12 (q : Pattern) (ha : d362362 q = 1) (hb : d363514 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362362, d363514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362362, d363514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100231 q ha hb
  have h13 (q : Pattern) (ha : d362363 q = 1) (hb : d363515 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362363, d363515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362363, d363515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362364 q = 1) (hb : d363516 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362364, d363516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362364, d363516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362365 q = 1) (hb : d363517 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362365, d363517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362365, d363517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d362366 q = 1) (hb : d363518 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362366, d363518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362366, d363518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362486 q = 1) (hb : d363611 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362486, d363611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362486, d363611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100245 q ha hb
  have h18 (q : Pattern) (ha : d362493 q = 1) (hb : d363622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362493, d363622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362493, d363622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100247 q ha hb
  have h19 (q : Pattern) (ha : d362494 q = 1) (hb : d363623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362494, d363623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d362494, d363623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d362495 q = 1) (hb : d363624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362495, d363624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362495, d363624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d362496 q = 1) (hb : d363625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362496, d363625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d362496, d363625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d362497 q = 1) (hb : d363626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362497, d363626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d362497, d363626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d362498 q = 1) (hb : d363627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d362498, d363627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362498, d363627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100249 (p : Pattern) (ha : d362504 p = 1) (hb : d363633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362499 q = 1) (hb : d363628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d362499, d363628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362499, d363628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100248 q ha hb
  have h2 (q : Pattern) (ha : d362500 q = 1) (hb : d363629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d362500, d363629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362500, d363629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362501 q = 1) (hb : d363630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d362501, d363630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362501, d363630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362502 q = 1) (hb : d363631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d362502, d363631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362502, d363631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362503 q = 1) (hb : d363632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d362503, d363632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362503, d363632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362504 q = 1) (hb : d363633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d362504, d363633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362504, d363633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
