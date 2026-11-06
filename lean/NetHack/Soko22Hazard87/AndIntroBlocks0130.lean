import NetHack.Soko22Hazard87.AndIntroBlocks0129
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro32500 (p : Pattern) (ha : d115422 p = 1) (hb : d135431 p = 1) : d161543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d135431 q = 1) : d161528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d161528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32496 q ha hb
    | true =>
      simp only [d13203, d161528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32497 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d135431 q = 1) : d161529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d161529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d161529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d135431 q = 1) : d161538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d161538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32499 q ha hb
    | true =>
      simp only [d13250, d161538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d135431 q = 1) : d161539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d161539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d161539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d135431 q = 1) : d161540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d161540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d161540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d135431 q = 1) : d161541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d161541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d161541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d135431 q = 1) : d161542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d161542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d161542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d135431 q = 1) : d161543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d161543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d161543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32501 (p : Pattern) (ha : d115428 p = 1) (hb : d135431 p = 1) : d161549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d135431 q = 1) : d161407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d161407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d161407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32465 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d135431 q = 1) : d161408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d161408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d161408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d135431 q = 1) : d161416 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d161416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32465 q ha hb
    | true =>
      simp only [d12998, d161416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32468 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d135431 q = 1) : d161417 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d161417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d161417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d135431 q = 1) : d161418 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d161418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d161418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d135431 q = 1) : d161484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d161484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32484 q ha hb
    | true =>
      simp only [d115406, d161484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32492 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d135431 q = 1) : d161491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d161491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32471 q ha hb
    | true =>
      simp only [d13141, d161491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32472 q ha hb
  have h8 (q : Pattern) (ha : d115407 q = 1) (hb : d135431 q = 1) : d161492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d161492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d161492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115408 q = 1) (hb : d135431 q = 1) : d161493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d161493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d161493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115409 q = 1) (hb : d135431 q = 1) : d161494 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d161494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d161494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115413 q = 1) (hb : d135431 q = 1) : d161498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d161498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d161498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32493 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d135431 q = 1) : d138689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d138689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d138689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32473 q ha hb
  have h13 (q : Pattern) (ha : d115414 q = 1) (hb : d135431 q = 1) : d161499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d161499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d161499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115415 q = 1) (hb : d135431 q = 1) : d161500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d161500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d161500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115416 q = 1) (hb : d135431 q = 1) : d161501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d161501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d161501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115417 q = 1) (hb : d135431 q = 1) : d161502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d161502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d161502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115423 q = 1) (hb : d135431 q = 1) : d161544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d161544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d161544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32500 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d135431 q = 1) : d138757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d138757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d138757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32476 q ha hb
  have h19 (q : Pattern) (ha : d115424 q = 1) (hb : d135431 q = 1) : d161545 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d161545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d161545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115425 q = 1) (hb : d135431 q = 1) : d161546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d161546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d161546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115426 q = 1) (hb : d135431 q = 1) : d161547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d161547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d161547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115427 q = 1) (hb : d135431 q = 1) : d161548 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d161548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d161548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115428 q = 1) (hb : d135431 q = 1) : d161549 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d161549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d161549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32502 (p : Pattern) (ha : d115434 p = 1) (hb : d135431 p = 1) : d161555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d135431 q = 1) : d161550 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d161550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d161550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32501 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d135431 q = 1) : d161551 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d161551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d161551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d135431 q = 1) : d161552 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d161552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d161552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d135431 q = 1) : d161553 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d161553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d161553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d135431 q = 1) : d161554 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d161554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d161554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d135431 q = 1) : d161555 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d161555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d161555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32503 (p : Pattern) (ha : d13293 p = 1) (hb : d135431 p = 1) : d161564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5120 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13283 q = 1) (hb : d135431 q = 1) : d138772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13283, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13284 q = 1) (hb : d135431 q = 1) : d138773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13285 q = 1) (hb : d135431 q = 1) : d138774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5120 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5139 q = 1) (hb : d94753 q = 1) : d5139 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5140 q = 1) (hb : d135431 q = 1) : d161559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d135431, d161559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5140, d135431, d161559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5141 q = 1) (hb : d135431 q = 1) : d161560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d161560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d161560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5142 q = 1) (hb : d135431 q = 1) : d161561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d161561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d161561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13286 q = 1) (hb : d135431 q = 1) : d161562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d161562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13286, d161562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13287 q = 1) (hb : d94753 q = 1) : d13287 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13288 q = 1) (hb : d135431 q = 1) : d138775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13288, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13289 q = 1) (hb : d135431 q = 1) : d138776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13290 q = 1) (hb : d135431 q = 1) : d138777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13291 q = 1) (hb : d135431 q = 1) : d138779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13291, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d13292 q = 1) (hb : d135431 q = 1) : d161563 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d161563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13292, d161563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13293 q = 1) (hb : d135431 q = 1) : d161564 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d161564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13293, d161564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro32504 (p : Pattern) (ha : d13297 p = 1) (hb : d135431 p = 1) : d138785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13287 q = 1) (hb : d94753 q = 1) : d13287 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13288 q = 1) (hb : d135431 q = 1) : d138775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13288, d135431, d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13289 q = 1) (hb : d135431 q = 1) : d138776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13290 q = 1) (hb : d135431 q = 1) : d138777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13291 q = 1) (hb : d135431 q = 1) : d138779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13291, d138779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13296 q = 1) (hb : d135431 q = 1) : d138784 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d138784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13296, d138784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13297 q = 1) (hb : d135431 q = 1) : d138785 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d138785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13297, d138785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32505 (p : Pattern) (ha : d13303 p = 1) (hb : d135431 p = 1) : d161570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d135431 q = 1) : d161567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d135431 q = 1) : d161568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d135431 q = 1) : d161569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d161569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d161569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d135431 q = 1) : d161570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d161570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d161570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32506 (p : Pattern) (ha : d13307 p = 1) (hb : d135431 p = 1) : d138795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d135431 q = 1) : d138794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d135431 q = 1) : d138795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d138795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d138795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32507 (p : Pattern) (ha : d13313 p = 1) (hb : d135431 p = 1) : d161576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d135431 q = 1) : d161571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d161571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32505 q ha hb
    | true =>
      simp only [d13308, d161571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32506 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d135431 q = 1) : d161572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d161572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d161572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d135431 q = 1) : d161573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d161573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d161573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d135431 q = 1) : d161574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d161574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d161574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d135431 q = 1) : d161575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d161575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d161575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d135431 q = 1) : d161576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d161576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d161576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32508 (p : Pattern) (ha : d13316 p = 1) (hb : d135431 p = 1) : d161579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d135431 q = 1) : d161567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d135431 q = 1) : d161568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d135431 q = 1) : d161569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d161569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d161569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d135431 q = 1) : d161579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d161579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d161579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32509 (p : Pattern) (ha : d13317 p = 1) (hb : d135431 p = 1) : d138805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d135431 q = 1) : d138794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d138794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d135431 q = 1) : d138805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d138805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d138805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32510 (p : Pattern) (ha : d13323 p = 1) (hb : d135431 p = 1) : d161585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d135431 q = 1) : d161571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d161571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32505 q ha hb
    | true =>
      simp only [d13308, d161571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32506 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d135431 q = 1) : d161572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d161572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d161572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d135431 q = 1) : d161573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d161573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d161573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d135431 q = 1) : d161574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d161574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d161574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d135431 q = 1) : d161575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d161575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d161575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d135431 q = 1) : d161580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d161580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32508 q ha hb
    | true =>
      simp only [d13318, d161580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32509 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d135431 q = 1) : d161581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d161581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d161581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d135431 q = 1) : d161582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d161582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d161582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d135431 q = 1) : d161583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d161583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d161583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d135431 q = 1) : d161584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d161584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d161584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d135431 q = 1) : d161585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d161585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d161585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32511 (p : Pattern) (ha : d13366 p = 1) (hb : d135431 p = 1) : d161611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5120 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13283 q = 1) (hb : d135431 q = 1) : d138772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13283, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13284 q = 1) (hb : d135431 q = 1) : d138773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13285 q = 1) (hb : d135431 q = 1) : d138774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5120 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5139 q = 1) (hb : d94753 q = 1) : d5139 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5140 q = 1) (hb : d135431 q = 1) : d161559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d135431, d161559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5140, d135431, d161559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5141 q = 1) (hb : d135431 q = 1) : d161560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d161560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d161560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5142 q = 1) (hb : d135431 q = 1) : d161561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d161561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d161561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13286 q = 1) (hb : d135431 q = 1) : d161562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d161562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13286, d161562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5143 q = 1) (hb : d135431 q = 1) : d161609 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d161609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5143, d161609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13365 q = 1) (hb : d135431 q = 1) : d161610 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d161610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13365, d161610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13366 q = 1) (hb : d135431 q = 1) : d161611 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d161611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13366, d161611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32512 (p : Pattern) (ha : d13376 p = 1) (hb : d135431 p = 1) : d161621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d135431 q = 1) : d161612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32511 q ha hb
    | true =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d135431 q = 1) : d161613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d135431 q = 1) : d161618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d161618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d161618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d135431 q = 1) : d161619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d161619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d161619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d135431 q = 1) : d161620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d161620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d161620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d135431 q = 1) : d161621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d161621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d161621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32513 (p : Pattern) (ha : d13460 p = 1) (hb : d135431 p = 1) : d161660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d135431 q = 1) : d161655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d161655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32512 q ha hb
    | true =>
      simp only [d13450, d161655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32506 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d135431 q = 1) : d161656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d161656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d161656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d135431 q = 1) : d161657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d161657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d161657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d135431 q = 1) : d161658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d161658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d161658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d135431 q = 1) : d161659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d161659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d161659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d135431 q = 1) : d138886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32506 q ha hb
    | true =>
      simp only [d13455, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d135431 q = 1) : d138887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d135431 q = 1) : d138888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d135431 q = 1) : d138889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d135431 q = 1) : d138890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d135431 q = 1) : d161660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d161660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d161660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32514 (p : Pattern) (ha : d13466 p = 1) (hb : d135431 p = 1) : d138897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d135431 q = 1) : d138886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32506 q ha hb
    | true =>
      simp only [d13455, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d135431 q = 1) : d138887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d135431 q = 1) : d138888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d135431 q = 1) : d138889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d135431 q = 1) : d138890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d135431 q = 1) : d138892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32509 q ha hb
    | true =>
      simp only [d13461, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d135431 q = 1) : d138893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d135431 q = 1) : d138894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d135431 q = 1) : d138895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d135431 q = 1) : d138896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d135431 q = 1) : d138897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d138897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d138897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32515 (p : Pattern) (ha : d13475 p = 1) (hb : d135431 p = 1) : d138906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d135431 q = 1) : d138892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32509 q ha hb
    | true =>
      simp only [d13461, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d135431 q = 1) : d138893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d135431 q = 1) : d138894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d135431 q = 1) : d138895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d135431 q = 1) : d138896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d135431 q = 1) : d138906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d138906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d138906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32516 (p : Pattern) (ha : d13522 p = 1) (hb : d135431 p = 1) : d138937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13516 q = 1) (hb : d94753 q = 1) : d13516 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13517 q = 1) (hb : d135431 q = 1) : d138919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13517, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13518 q = 1) (hb : d135431 q = 1) : d138920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13519 q = 1) (hb : d135431 q = 1) : d138921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13520 q = 1) (hb : d135431 q = 1) : d138927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13520, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13521 q = 1) (hb : d135431 q = 1) : d138936 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d138936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13521, d138936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13522 q = 1) (hb : d135431 q = 1) : d138937 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d138937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13522, d138937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32517 (p : Pattern) (ha : d13586 p = 1) (hb : d135431 p = 1) : d138968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d135431 q = 1) : d138938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32516 q ha hb
    | true =>
      simp only [d13523, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d135431 q = 1) : d138939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d135431 q = 1) : d138965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d138965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d138965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d135431 q = 1) : d138966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d138966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d138966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d135431 q = 1) : d138967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d138967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d138967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d135431 q = 1) : d138968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d138968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d138968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32518 (p : Pattern) (ha : d13592 p = 1) (hb : d135431 p = 1) : d138974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d135431 q = 1) : d138969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d138969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32517 q ha hb
    | true =>
      simp only [d13587, d138969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d135431 q = 1) : d138970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d138970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d138970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d135431 q = 1) : d138971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d138971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d138971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d135431 q = 1) : d138972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d138972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d138972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d135431 q = 1) : d138973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d138973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d138973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d135431 q = 1) : d138974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d138974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d138974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32519 (p : Pattern) (ha : d13328 p = 1) (hb : d135431 p = 1) : d161590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d135431 q = 1) : d161567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d135431 q = 1) : d161568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d135431 q = 1) : d161589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d161589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d161589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d135431 q = 1) : d161590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d161590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d161590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32520 (p : Pattern) (ha : d13330 p = 1) (hb : d135431 p = 1) : d138818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d135431 q = 1) : d138817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d135431 q = 1) : d138818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d138818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d138818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32521 (p : Pattern) (ha : d13337 p = 1) (hb : d135431 p = 1) : d161597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d135431 q = 1) : d161567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d135431 q = 1) : d161595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d161595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d161595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d135431 q = 1) : d161596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d161596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d161596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d135431 q = 1) : d161597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d161597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d161597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32522 (p : Pattern) (ha : d13340 p = 1) (hb : d135431 p = 1) : d138828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d135431 q = 1) : d138826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d135431 q = 1) : d138827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d135431 q = 1) : d138828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d138828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d138828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32523 (p : Pattern) (ha : d13362 p = 1) (hb : d135431 p = 1) : d161606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13282 q = 1) (hb : d94753 q = 1) : d13282 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13345 q = 1) (hb : d135431 q = 1) : d138832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d135431, d138832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13345, d135431, d138832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13346 q = 1) (hb : d135431 q = 1) : d138833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d138833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d138833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13347 q = 1) (hb : d135431 q = 1) : d138834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d138834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d138834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13282 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13356 q = 1) (hb : d94753 q = 1) : d13356 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13357 q = 1) (hb : d135431 q = 1) : d161601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d135431, d161601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13357, d135431, d161601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13358 q = 1) (hb : d135431 q = 1) : d161602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d161602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13358, d161602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13359 q = 1) (hb : d135431 q = 1) : d161603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d161603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13359, d161603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13360 q = 1) (hb : d135431 q = 1) : d161604 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d161604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13360, d161604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5120 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13283 q = 1) (hb : d135431 q = 1) : d138772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13283, d135431, d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13284 q = 1) (hb : d135431 q = 1) : d138773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13285 q = 1) (hb : d135431 q = 1) : d138774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d5120 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5139 q = 1) (hb : d94753 q = 1) : d5139 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d5140 q = 1) (hb : d135431 q = 1) : d161559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d135431, d161559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d5140, d135431, d161559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5141 q = 1) (hb : d135431 q = 1) : d161560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d161560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d161560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5142 q = 1) (hb : d135431 q = 1) : d161561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d161561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d161561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13286 q = 1) (hb : d135431 q = 1) : d161562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d161562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13286, d161562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13361 q = 1) (hb : d135431 q = 1) : d161605 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d161605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13361, d161605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13362 q = 1) (hb : d135431 q = 1) : d161606 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d161606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13362, d161606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32524 (p : Pattern) (ha : d13372 p = 1) (hb : d135431 p = 1) : d161617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d135431 q = 1) : d161607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d161607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32523 q ha hb
    | true =>
      simp only [d13363, d161607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d135431 q = 1) : d161608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d161608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d161608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d135431 q = 1) : d161612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32511 q ha hb
    | true =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d135431 q = 1) : d161613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d135431 q = 1) : d161614 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d161614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d161614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d135431 q = 1) : d161615 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d161615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d161615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d135431 q = 1) : d161616 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d161616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d161616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d135431 q = 1) : d161617 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d161617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d161617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32525 (p : Pattern) (ha : d13417 p = 1) (hb : d135431 p = 1) : d161627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d135431 q = 1) : d161624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d161624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d161624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d135431 q = 1) : d161625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d161625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d161625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d135431 q = 1) : d161626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d161626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d161626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d135431 q = 1) : d161627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d161627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d161627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32526 (p : Pattern) (ha : d115442 p = 1) (hb : d135431 p = 1) : d161633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d135431 q = 1) : d161591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d161591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32519 q ha hb
    | true =>
      simp only [d13331, d161591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32520 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d135431 q = 1) : d161592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d161592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d161592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d135431 q = 1) : d161593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d161593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d161593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d135431 q = 1) : d161594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d161594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d161594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d135431 q = 1) : d161598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d161598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32521 q ha hb
    | true =>
      simp only [d13341, d161598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32522 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d135431 q = 1) : d161599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d161599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d161599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d135431 q = 1) : d161600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d161600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d161600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d135431 q = 1) : d161622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d161622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32524 q ha hb
    | true =>
      simp only [d13377, d161622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32512 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d135431 q = 1) : d161623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d161623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d161623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d135431 q = 1) : d161628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d161628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32525 q ha hb
    | true =>
      simp only [d13418, d161628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d135431 q = 1) : d161629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d161629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d161629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d135431 q = 1) : d161630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d161630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d161630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d135431 q = 1) : d161631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d161631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d161631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d135431 q = 1) : d161632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d161632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d161632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115442 q = 1) (hb : d135431 q = 1) : d161633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d161633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d161633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32527 (p : Pattern) (ha : d13424 p = 1) (hb : d135431 p = 1) : d161634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d135431 q = 1) : d161567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d135431 q = 1) : d161568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d161568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d135431 q = 1) : d161589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d161589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d161589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13424 q = 1) (hb : d135431 q = 1) : d161634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d161634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13424, d161634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32528 (p : Pattern) (ha : d13425 p = 1) (hb : d135431 p = 1) : d138865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d135431 q = 1) : d138793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d135431 q = 1) : d138817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13425 q = 1) (hb : d135431 q = 1) : d138865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, d138865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13425, d138865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32529 (p : Pattern) (ha : d13430 p = 1) (hb : d135431 p = 1) : d161639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d135431 q = 1) : d161567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d161567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d135431 q = 1) : d161595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d161595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d161595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d135431 q = 1) : d161596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d161596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d161596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13430 q = 1) (hb : d135431 q = 1) : d161639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d161639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13430, d161639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32530 (p : Pattern) (ha : d13431 p = 1) (hb : d135431 p = 1) : d138871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d135431 q = 1) : d138792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d135431 q = 1) : d138826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d135431 q = 1) : d138827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13431 q = 1) (hb : d135431 q = 1) : d138871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, d138871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13431, d138871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32531 (p : Pattern) (ha : d13435 p = 1) (hb : d135431 p = 1) : d161643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d135431 q = 1) : d161607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d161607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32523 q ha hb
    | true =>
      simp only [d13363, d161607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d135431 q = 1) : d161608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d161608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d161608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d135431 q = 1) : d161612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32511 q ha hb
    | true =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d135431 q = 1) : d161613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d135431 q = 1) : d161614 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d161614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d161614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d135431 q = 1) : d161615 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d161615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d161615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d135431 q = 1) : d161616 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d161616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d161616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d135431 q = 1) : d161643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d161643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d161643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32532 (p : Pattern) (ha : d13436 p = 1) (hb : d135431 p = 1) : d161644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d135431 q = 1) : d161612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32511 q ha hb
    | true =>
      simp only [d13367, d161612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d135431 q = 1) : d161613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d161613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d135431 q = 1) : d138786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32504 q ha hb
    | true =>
      simp only [d13298, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d135431 q = 1) : d138787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d135431 q = 1) : d161618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d161618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d161618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d135431 q = 1) : d161619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d161619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d161619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d135431 q = 1) : d161620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d161620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d161620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13436 q = 1) (hb : d135431 q = 1) : d161644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d161644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13436, d161644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32533 (p : Pattern) (ha : d13442 p = 1) (hb : d135431 p = 1) : d161647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d135431 q = 1) : d161565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32503 q ha hb
    | true =>
      simp only [d13294, d161565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d135431 q = 1) : d161566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d161566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d135431 q = 1) : d161624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d161624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d161624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d135431 q = 1) : d161625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d161625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d161625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d135431 q = 1) : d161626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d161626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d161626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d135431 q = 1) : d161647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d161647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d161647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32534 (p : Pattern) (ha : d115447 p = 1) (hb : d135431 p = 1) : d161653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d135431 q = 1) : d161591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d161591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32519 q ha hb
    | true =>
      simp only [d13331, d161591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32520 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d135431 q = 1) : d161592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d161592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d161592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d135431 q = 1) : d161593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d161593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d161593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d135431 q = 1) : d161594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d161594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d161594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d135431 q = 1) : d161598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d161598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32521 q ha hb
    | true =>
      simp only [d13341, d161598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32522 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d135431 q = 1) : d161599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d161599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d161599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d135431 q = 1) : d161600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d161600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d161600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d135431 q = 1) : d161622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d161622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32524 q ha hb
    | true =>
      simp only [d13377, d161622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32512 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d135431 q = 1) : d161623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d161623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d161623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d135431 q = 1) : d161628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d161628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32525 q ha hb
    | true =>
      simp only [d13418, d161628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d135431 q = 1) : d161629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d161629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d161629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d135431 q = 1) : d161630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d161630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d161630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d135431 q = 1) : d161631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d161631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d161631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d135431 q = 1) : d161632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d161632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d161632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13426 q = 1) (hb : d135431 q = 1) : d161635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d161635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32527 q ha hb
    | true =>
      simp only [d13426, d161635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32528 q ha hb
  have h16 (q : Pattern) (ha : d13427 q = 1) (hb : d135431 q = 1) : d161636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d161636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d161636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13428 q = 1) (hb : d135431 q = 1) : d161637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d161637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13428, d161637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13429 q = 1) (hb : d135431 q = 1) : d161638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d161638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d161638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13432 q = 1) (hb : d135431 q = 1) : d161640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d161640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32529 q ha hb
    | true =>
      simp only [d13432, d161640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32530 q ha hb
  have h20 (q : Pattern) (ha : d13433 q = 1) (hb : d135431 q = 1) : d161641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d161641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d161641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13434 q = 1) (hb : d135431 q = 1) : d161642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d161642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13434, d161642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13437 q = 1) (hb : d135431 q = 1) : d161645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d161645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32531 q ha hb
    | true =>
      simp only [d13437, d161645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32532 q ha hb
  have h23 (q : Pattern) (ha : d115443 q = 1) (hb : d135431 q = 1) : d161646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d161646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115443, d161646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13443 q = 1) (hb : d135431 q = 1) : d161648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d161648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32533 q ha hb
    | true =>
      simp only [d13443, d161648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13444 q = 1) (hb : d135431 q = 1) : d161649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d161649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13444, d161649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115444 q = 1) (hb : d135431 q = 1) : d161650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d161650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115444, d161650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115445 q = 1) (hb : d135431 q = 1) : d161651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d161651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115445, d161651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115446 q = 1) (hb : d135431 q = 1) : d161652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d161652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115446, d161652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115447 q = 1) (hb : d135431 q = 1) : d161653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d161653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115447, d161653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32535 (p : Pattern) (ha : d115454 p = 1) (hb : d135431 p = 1) : d161667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d135431 q = 1) : d161645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d161645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32531 q ha hb
    | true =>
      simp only [d13437, d161645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32532 q ha hb
  have h2 (q : Pattern) (ha : d115443 q = 1) (hb : d135431 q = 1) : d161646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d161646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115443, d161646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d135431 q = 1) : d161648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d161648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32533 q ha hb
    | true =>
      simp only [d13443, d161648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d135431 q = 1) : d161649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d161649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d161649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d135431 q = 1) : d161650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d161650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d161650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d135431 q = 1) : d161665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d161665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d161665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d135431 q = 1) : d161666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d161666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d161666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d135431 q = 1) : d161667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d161667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d161667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32536 (p : Pattern) (ha : d13505 p = 1) (hb : d135431 p = 1) : d161682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13481 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13482 q = 1) (hb : d94753 q = 1) : d13482 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13483 q = 1) (hb : d135431 q = 1) : d138912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, d135431, d138912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13483, d135431, d138912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13484 q = 1) (hb : d135431 q = 1) : d138913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, d138913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13484, d138913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13485 q = 1) (hb : d135431 q = 1) : d138914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, d138914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13485, d138914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13482 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13495 q = 1) (hb : d94753 q = 1) : d13495 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13496 q = 1) (hb : d135431 q = 1) : d161673 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13496, d135431, d161673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13496, d135431, d161673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13497 q = 1) (hb : d135431 q = 1) : d161674 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13497, d161674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13497, d161674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13498 q = 1) (hb : d135431 q = 1) : d161675 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13498, d161675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13498, d161675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13499 q = 1) (hb : d135431 q = 1) : d161676 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d161676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13499, d161676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6495 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13500 q = 1) (hb : d135431 q = 1) : d138915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13500, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13501 q = 1) (hb : d135431 q = 1) : d138916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13502 q = 1) (hb : d135431 q = 1) : d138917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d6495 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6501 q = 1) (hb : d94753 q = 1) : d6501 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6502 q = 1) (hb : d135431 q = 1) : d161677 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d135431, d161677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d6502, d135431, d161677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6503 q = 1) (hb : d135431 q = 1) : d161678 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d161678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d161678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6504 q = 1) (hb : d135431 q = 1) : d161679 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d161679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d161679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13503 q = 1) (hb : d135431 q = 1) : d161680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d161680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13503, d161680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13504 q = 1) (hb : d135431 q = 1) : d161681 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d161681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13504, d161681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13505 q = 1) (hb : d135431 q = 1) : d161682 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d161682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13505, d161682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32537 (p : Pattern) (ha : d13509 p = 1) (hb : d135431 p = 1) : d161687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6495 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13500 q = 1) (hb : d135431 q = 1) : d138915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13500, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13501 q = 1) (hb : d135431 q = 1) : d138916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13502 q = 1) (hb : d135431 q = 1) : d138917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6495 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6501 q = 1) (hb : d94753 q = 1) : d6501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6502 q = 1) (hb : d135431 q = 1) : d161677 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d135431, d161677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6502, d135431, d161677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6503 q = 1) (hb : d135431 q = 1) : d161678 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d161678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d161678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6504 q = 1) (hb : d135431 q = 1) : d161679 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d161679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d161679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13503 q = 1) (hb : d135431 q = 1) : d161680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d161680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13503, d161680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6505 q = 1) (hb : d135431 q = 1) : d161685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d161685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6505, d161685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13508 q = 1) (hb : d135431 q = 1) : d161686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d161686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13508, d161686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13509 q = 1) (hb : d135431 q = 1) : d161687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d161687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13509, d161687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32538 (p : Pattern) (ha : d13515 p = 1) (hb : d135431 p = 1) : d161693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d135431 q = 1) : d161683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d161683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32536 q ha hb
    | true =>
      simp only [d13506, d161683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d135431 q = 1) : d161684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d161684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d161684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d135431 q = 1) : d161688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d161688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32537 q ha hb
    | true =>
      simp only [d13510, d161688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d135431 q = 1) : d161689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d161689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d161689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d135431 q = 1) : d161690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d161690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d161690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d135431 q = 1) : d161691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d161691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d161691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d135431 q = 1) : d161692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d161692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d161692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d135431 q = 1) : d161693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d161693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d161693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32539 (p : Pattern) (ha : d13528 p = 1) (hb : d135431 p = 1) : d161697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d135431 q = 1) : d161688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d161688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32537 q ha hb
    | true =>
      simp only [d13510, d161688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d135431 q = 1) : d161689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d161689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d161689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d135431 q = 1) : d138938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32516 q ha hb
    | true =>
      simp only [d13523, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d135431 q = 1) : d138939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13525 q = 1) (hb : d135431 q = 1) : d161694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d161694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d161694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13526 q = 1) (hb : d135431 q = 1) : d161695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d161695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13526, d161695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13527 q = 1) (hb : d135431 q = 1) : d161696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d161696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13527, d161696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13528 q = 1) (hb : d135431 q = 1) : d161697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d161697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13528, d161697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32540 (p : Pattern) (ha : d13569 p = 1) (hb : d135431 p = 1) : d161701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6495 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13500 q = 1) (hb : d135431 q = 1) : d138915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13500, d135431, d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13501 q = 1) (hb : d135431 q = 1) : d138916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13502 q = 1) (hb : d135431 q = 1) : d138917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6495 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6501 q = 1) (hb : d94753 q = 1) : d6501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6502 q = 1) (hb : d135431 q = 1) : d161677 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d135431, d161677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6502, d135431, d161677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6503 q = 1) (hb : d135431 q = 1) : d161678 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d161678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d161678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6504 q = 1) (hb : d135431 q = 1) : d161679 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d161679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d161679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13503 q = 1) (hb : d135431 q = 1) : d161680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d161680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13503, d161680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13516 q = 1) (hb : d94753 q = 1) : d13516 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13517 q = 1) (hb : d135431 q = 1) : d138919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13517, d135431, d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13518 q = 1) (hb : d135431 q = 1) : d138920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13519 q = 1) (hb : d135431 q = 1) : d138921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13520 q = 1) (hb : d135431 q = 1) : d138927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13520, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d13568 q = 1) (hb : d135431 q = 1) : d161700 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d161700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13568, d161700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13569 q = 1) (hb : d135431 q = 1) : d161701 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d161701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13569, d161701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro32541 (p : Pattern) (ha : d13575 p = 1) (hb : d135431 p = 1) : d161707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d135431 q = 1) : d161702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d161702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32540 q ha hb
    | true =>
      simp only [d13570, d161702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d135431 q = 1) : d161703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d161703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d161703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d135431 q = 1) : d161704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d161704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d161704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d135431 q = 1) : d161705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d161705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d161705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d135431 q = 1) : d161706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d161706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d161706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d135431 q = 1) : d161707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d161707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d161707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32542 (p : Pattern) (ha : d115464 p = 1) (hb : d135431 p = 1) : d161713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d135431 q = 1) : d161698 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d161698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32538 q ha hb
    | true =>
      simp only [d13529, d161698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32539 q ha hb
  have h2 (q : Pattern) (ha : d115460 q = 1) (hb : d135431 q = 1) : d161699 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d161699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115460, d161699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d135431 q = 1) : d161708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d161708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32541 q ha hb
    | true =>
      simp only [d13576, d161708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d135431 q = 1) : d161709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d161709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d161709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d135431 q = 1) : d161710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d161710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d161710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d135431 q = 1) : d161711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d161711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d161711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d135431 q = 1) : d161712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d161712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d161712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d135431 q = 1) : d161713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d161713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d161713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32543 (p : Pattern) (ha : d115470 p = 1) (hb : d135431 p = 1) : d161719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d135431 q = 1) : d161577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d161577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d161577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32507 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d135431 q = 1) : d161578 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d161578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d161578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d135431 q = 1) : d161586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d161586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32507 q ha hb
    | true =>
      simp only [d13324, d161586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32510 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d135431 q = 1) : d161587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d161587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d161587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d135431 q = 1) : d161588 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d161588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d161588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115448 q = 1) (hb : d135431 q = 1) : d161654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d161654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32526 q ha hb
    | true =>
      simp only [d115448, d161654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32534 q ha hb
  have h7 (q : Pattern) (ha : d13467 q = 1) (hb : d135431 q = 1) : d161661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d161661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32513 q ha hb
    | true =>
      simp only [d13467, d161661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32514 q ha hb
  have h8 (q : Pattern) (ha : d115449 q = 1) (hb : d135431 q = 1) : d161662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d161662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d161662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115450 q = 1) (hb : d135431 q = 1) : d161663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d161663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115450, d161663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115451 q = 1) (hb : d135431 q = 1) : d161664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d161664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115451, d161664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115455 q = 1) (hb : d135431 q = 1) : d161668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d161668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115455, d161668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32535 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d135431 q = 1) : d138907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, d138907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, d138907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32515 q ha hb
  have h13 (q : Pattern) (ha : d115456 q = 1) (hb : d135431 q = 1) : d161669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d161669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115456, d161669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115457 q = 1) (hb : d135431 q = 1) : d161670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d161670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115457, d161670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115458 q = 1) (hb : d135431 q = 1) : d161671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d161671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115458, d161671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115459 q = 1) (hb : d135431 q = 1) : d161672 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d161672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115459, d161672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115465 q = 1) (hb : d135431 q = 1) : d161714 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d161714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115465, d161714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32542 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d135431 q = 1) : d138975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, d138975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, d138975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32518 q ha hb
  have h19 (q : Pattern) (ha : d115466 q = 1) (hb : d135431 q = 1) : d161715 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d161715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115466, d161715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115467 q = 1) (hb : d135431 q = 1) : d161716 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d161716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115467, d161716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115468 q = 1) (hb : d135431 q = 1) : d161717 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d161717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115468, d161717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115469 q = 1) (hb : d135431 q = 1) : d161718 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d161718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115469, d161718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115470 q = 1) (hb : d135431 q = 1) : d161719 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d161719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115470, d161719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32544 (p : Pattern) (ha : d115476 p = 1) (hb : d135431 p = 1) : d161725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d135431 q = 1) : d161720 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d161720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d161720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32543 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d135431 q = 1) : d161721 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d161721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d161721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d135431 q = 1) : d161722 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d161722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d161722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d135431 q = 1) : d161723 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d161723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d161723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d135431 q = 1) : d161724 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d161724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d161724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d135431 q = 1) : d161725 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d161725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d161725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32545 (p : Pattern) (ha : d13620 p = 1) (hb : d135431 p = 1) : d161735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5237 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13610 q = 1) (hb : d135431 q = 1) : d138991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13610, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13611 q = 1) (hb : d135431 q = 1) : d138992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13612 q = 1) (hb : d135431 q = 1) : d138993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5237 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5252 q = 1) (hb : d94753 q = 1) : d5252 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5253 q = 1) (hb : d135431 q = 1) : d161730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d135431, d161730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5253, d135431, d161730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5254 q = 1) (hb : d135431 q = 1) : d161731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d161731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d161731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5255 q = 1) (hb : d135431 q = 1) : d161732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d161732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d161732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13613 q = 1) (hb : d135431 q = 1) : d161733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d161733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13613, d161733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13614 q = 1) (hb : d94753 q = 1) : d13614 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13615 q = 1) (hb : d135431 q = 1) : d138994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13615, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13616 q = 1) (hb : d135431 q = 1) : d138995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13617 q = 1) (hb : d135431 q = 1) : d138996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13618 q = 1) (hb : d135431 q = 1) : d138998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13618, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d13619 q = 1) (hb : d135431 q = 1) : d161734 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d161734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13619, d161734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13620 q = 1) (hb : d135431 q = 1) : d161735 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d161735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13620, d161735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro32546 (p : Pattern) (ha : d13624 p = 1) (hb : d135431 p = 1) : d139004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5237 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13614 q = 1) (hb : d94753 q = 1) : d13614 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13615 q = 1) (hb : d135431 q = 1) : d138994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13615, d135431, d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13616 q = 1) (hb : d135431 q = 1) : d138995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13617 q = 1) (hb : d135431 q = 1) : d138996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13618 q = 1) (hb : d135431 q = 1) : d138998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13618, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13623 q = 1) (hb : d135431 q = 1) : d139003 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, d139003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13623, d139003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13624 q = 1) (hb : d135431 q = 1) : d139004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, d139004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13624, d139004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32547 (p : Pattern) (ha : d13630 p = 1) (hb : d135431 p = 1) : d161741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d135431 q = 1) : d161738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d135431 q = 1) : d161739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d135431 q = 1) : d161740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d161740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d161740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13630 q = 1) (hb : d135431 q = 1) : d161741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d161741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d161741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32548 (p : Pattern) (ha : d13634 p = 1) (hb : d135431 p = 1) : d139014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d135431 q = 1) : d139013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13634 q = 1) (hb : d135431 q = 1) : d139014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, d139014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13634, d139014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32549 (p : Pattern) (ha : d13640 p = 1) (hb : d135431 p = 1) : d161747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d135431 q = 1) : d161742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d161742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32547 q ha hb
    | true =>
      simp only [d13635, d161742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32548 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d135431 q = 1) : d161743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d161743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d161743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d135431 q = 1) : d161744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d161744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d161744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d135431 q = 1) : d161745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d161745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d161745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d135431 q = 1) : d161746 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d161746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d161746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13640 q = 1) (hb : d135431 q = 1) : d161747 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d161747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d161747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32550 (p : Pattern) (ha : d13643 p = 1) (hb : d135431 p = 1) : d161750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d135431 q = 1) : d161738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d135431 q = 1) : d161739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d135431 q = 1) : d161740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d161740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d161740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13643 q = 1) (hb : d135431 q = 1) : d161750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d161750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13643, d161750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32551 (p : Pattern) (ha : d13644 p = 1) (hb : d135431 p = 1) : d139024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d135431 q = 1) : d139013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13644 q = 1) (hb : d135431 q = 1) : d139024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, d139024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13644, d139024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32552 (p : Pattern) (ha : d13650 p = 1) (hb : d135431 p = 1) : d161756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d135431 q = 1) : d161742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d161742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32547 q ha hb
    | true =>
      simp only [d13635, d161742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32548 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d135431 q = 1) : d161743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d161743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d161743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d135431 q = 1) : d161744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d161744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d161744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d135431 q = 1) : d161745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d161745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d161745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d135431 q = 1) : d161746 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d161746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d161746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13645 q = 1) (hb : d135431 q = 1) : d161751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d161751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32550 q ha hb
    | true =>
      simp only [d13645, d161751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32551 q ha hb
  have h7 (q : Pattern) (ha : d13646 q = 1) (hb : d135431 q = 1) : d161752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d161752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d161752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13647 q = 1) (hb : d135431 q = 1) : d161753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d161753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13647, d161753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13648 q = 1) (hb : d135431 q = 1) : d161754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d161754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d161754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13649 q = 1) (hb : d135431 q = 1) : d161755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d161755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d161755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13650 q = 1) (hb : d135431 q = 1) : d161756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d161756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13650, d161756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32553 (p : Pattern) (ha : d13693 p = 1) (hb : d135431 p = 1) : d161782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5237 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13610 q = 1) (hb : d135431 q = 1) : d138991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13610, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13611 q = 1) (hb : d135431 q = 1) : d138992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13612 q = 1) (hb : d135431 q = 1) : d138993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5237 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5252 q = 1) (hb : d94753 q = 1) : d5252 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5253 q = 1) (hb : d135431 q = 1) : d161730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d135431, d161730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5253, d135431, d161730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5254 q = 1) (hb : d135431 q = 1) : d161731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d161731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d161731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5255 q = 1) (hb : d135431 q = 1) : d161732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d161732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d161732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13613 q = 1) (hb : d135431 q = 1) : d161733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d161733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13613, d161733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5256 q = 1) (hb : d135431 q = 1) : d161780 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d161780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5256, d161780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13692 q = 1) (hb : d135431 q = 1) : d161781 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d161781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13692, d161781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13693 q = 1) (hb : d135431 q = 1) : d161782 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d161782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13693, d161782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32554 (p : Pattern) (ha : d13703 p = 1) (hb : d135431 p = 1) : d161792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d135431 q = 1) : d161783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32553 q ha hb
    | true =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d135431 q = 1) : d161784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d135431 q = 1) : d161789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d161789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d161789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d135431 q = 1) : d161790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d161790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d161790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d135431 q = 1) : d161791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d161791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d161791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13703 q = 1) (hb : d135431 q = 1) : d161792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d161792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d161792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32555 (p : Pattern) (ha : d13787 p = 1) (hb : d135431 p = 1) : d161831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13777 q = 1) (hb : d135431 q = 1) : d161826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d161826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32554 q ha hb
    | true =>
      simp only [d13777, d161826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32548 q ha hb
  have h2 (q : Pattern) (ha : d13778 q = 1) (hb : d135431 q = 1) : d161827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d161827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d161827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13779 q = 1) (hb : d135431 q = 1) : d161828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d161828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13779, d161828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13780 q = 1) (hb : d135431 q = 1) : d161829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d161829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d161829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13781 q = 1) (hb : d135431 q = 1) : d161830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d161830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d161830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13782 q = 1) (hb : d135431 q = 1) : d139105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32548 q ha hb
    | true =>
      simp only [d13782, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13783 q = 1) (hb : d135431 q = 1) : d139106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13784 q = 1) (hb : d135431 q = 1) : d139107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13784, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13785 q = 1) (hb : d135431 q = 1) : d139108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13786 q = 1) (hb : d135431 q = 1) : d139109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13787 q = 1) (hb : d135431 q = 1) : d161831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d161831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13787, d161831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32556 (p : Pattern) (ha : d13793 p = 1) (hb : d135431 p = 1) : d139116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13782 q = 1) (hb : d135431 q = 1) : d139105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32548 q ha hb
    | true =>
      simp only [d13782, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13783 q = 1) (hb : d135431 q = 1) : d139106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13784 q = 1) (hb : d135431 q = 1) : d139107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13784, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13785 q = 1) (hb : d135431 q = 1) : d139108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13786 q = 1) (hb : d135431 q = 1) : d139109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13788 q = 1) (hb : d135431 q = 1) : d139111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32551 q ha hb
    | true =>
      simp only [d13788, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13789 q = 1) (hb : d135431 q = 1) : d139112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13790 q = 1) (hb : d135431 q = 1) : d139113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13790, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13791 q = 1) (hb : d135431 q = 1) : d139114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13792 q = 1) (hb : d135431 q = 1) : d139115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13793 q = 1) (hb : d135431 q = 1) : d139116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, d139116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13793, d139116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32557 (p : Pattern) (ha : d13802 p = 1) (hb : d135431 p = 1) : d139125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13788 q = 1) (hb : d135431 q = 1) : d139111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32551 q ha hb
    | true =>
      simp only [d13788, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13789 q = 1) (hb : d135431 q = 1) : d139112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13790 q = 1) (hb : d135431 q = 1) : d139113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13790, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13791 q = 1) (hb : d135431 q = 1) : d139114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13792 q = 1) (hb : d135431 q = 1) : d139115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13802 q = 1) (hb : d135431 q = 1) : d139125 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, d139125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13802, d139125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32558 (p : Pattern) (ha : d13849 p = 1) (hb : d135431 p = 1) : d139156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13843 q = 1) (hb : d94753 q = 1) : d13843 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13844 q = 1) (hb : d135431 q = 1) : d139138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13844, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13845 q = 1) (hb : d135431 q = 1) : d139139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13846 q = 1) (hb : d135431 q = 1) : d139140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13847 q = 1) (hb : d135431 q = 1) : d139146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13847, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13848 q = 1) (hb : d135431 q = 1) : d139155 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, d139155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13848, d139155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13849 q = 1) (hb : d135431 q = 1) : d139156 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, d139156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13849, d139156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32559 (p : Pattern) (ha : d13913 p = 1) (hb : d135431 p = 1) : d139187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13850 q = 1) (hb : d135431 q = 1) : d139157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32558 q ha hb
    | true =>
      simp only [d13850, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13851 q = 1) (hb : d135431 q = 1) : d139158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13910 q = 1) (hb : d135431 q = 1) : d139184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, d139184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13910, d139184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13911 q = 1) (hb : d135431 q = 1) : d139185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, d139185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13911, d139185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13912 q = 1) (hb : d135431 q = 1) : d139186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, d139186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13912, d139186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13913 q = 1) (hb : d135431 q = 1) : d139187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, d139187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13913, d139187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32560 (p : Pattern) (ha : d13919 p = 1) (hb : d135431 p = 1) : d139193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13914 q = 1) (hb : d135431 q = 1) : d139188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, d139188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32559 q ha hb
    | true =>
      simp only [d13914, d139188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13915 q = 1) (hb : d135431 q = 1) : d139189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, d139189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13915, d139189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13916 q = 1) (hb : d135431 q = 1) : d139190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, d139190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13916, d139190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13917 q = 1) (hb : d135431 q = 1) : d139191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, d139191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13917, d139191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13918 q = 1) (hb : d135431 q = 1) : d139192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, d139192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13918, d139192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13919 q = 1) (hb : d135431 q = 1) : d139193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, d139193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13919, d139193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32561 (p : Pattern) (ha : d13655 p = 1) (hb : d135431 p = 1) : d161761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d135431 q = 1) : d161738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d135431 q = 1) : d161739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d135431 q = 1) : d161760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d161760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d161760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13655 q = 1) (hb : d135431 q = 1) : d161761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d161761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d161761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32562 (p : Pattern) (ha : d13657 p = 1) (hb : d135431 p = 1) : d139037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d135431 q = 1) : d139036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13657 q = 1) (hb : d135431 q = 1) : d139037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, d139037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13657, d139037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32563 (p : Pattern) (ha : d13664 p = 1) (hb : d135431 p = 1) : d161768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d135431 q = 1) : d161738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d135431 q = 1) : d161766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d161766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d161766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d135431 q = 1) : d161767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d161767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d161767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13664 q = 1) (hb : d135431 q = 1) : d161768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d161768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d161768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32564 (p : Pattern) (ha : d13667 p = 1) (hb : d135431 p = 1) : d139047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d135431 q = 1) : d139045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d135431 q = 1) : d139046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d135431 q = 1) : d139047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, d139047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13667, d139047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32565 (p : Pattern) (ha : d13689 p = 1) (hb : d135431 p = 1) : d161777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13671 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13609 q = 1) (hb : d94753 q = 1) : d13609 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13672 q = 1) (hb : d135431 q = 1) : d139051 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13672, d135431, d139051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13672, d135431, d139051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13673 q = 1) (hb : d135431 q = 1) : d139052 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13673, d139052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13673, d139052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13674 q = 1) (hb : d135431 q = 1) : d139053 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13674, d139053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13674, d139053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13609 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13683 q = 1) (hb : d94753 q = 1) : d13683 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13684 q = 1) (hb : d135431 q = 1) : d161772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13684, d135431, d161772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13684, d135431, d161772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13685 q = 1) (hb : d135431 q = 1) : d161773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13685, d161773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13685, d161773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13686 q = 1) (hb : d135431 q = 1) : d161774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13686, d161774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13686, d161774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13687 q = 1) (hb : d135431 q = 1) : d161775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d161775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13687, d161775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5237 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13610 q = 1) (hb : d135431 q = 1) : d138991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13610, d135431, d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13611 q = 1) (hb : d135431 q = 1) : d138992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13612 q = 1) (hb : d135431 q = 1) : d138993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d5237 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5252 q = 1) (hb : d94753 q = 1) : d5252 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d5253 q = 1) (hb : d135431 q = 1) : d161730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d135431, d161730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d5253, d135431, d161730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5254 q = 1) (hb : d135431 q = 1) : d161731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d161731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d161731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5255 q = 1) (hb : d135431 q = 1) : d161732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d161732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d161732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13613 q = 1) (hb : d135431 q = 1) : d161733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d161733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13613, d161733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13688 q = 1) (hb : d135431 q = 1) : d161776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d161776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13688, d161776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13689 q = 1) (hb : d135431 q = 1) : d161777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d161777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13689, d161777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32566 (p : Pattern) (ha : d13699 p = 1) (hb : d135431 p = 1) : d161788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d135431 q = 1) : d161778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d161778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32565 q ha hb
    | true =>
      simp only [d13690, d161778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d135431 q = 1) : d161779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d161779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d161779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d135431 q = 1) : d161783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32553 q ha hb
    | true =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d135431 q = 1) : d161784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d135431 q = 1) : d161785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d161785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d161785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d135431 q = 1) : d161786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d161786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d161786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d135431 q = 1) : d161787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d161787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d161787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d135431 q = 1) : d161788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d161788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d161788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32567 (p : Pattern) (ha : d13744 p = 1) (hb : d135431 p = 1) : d161798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d135431 q = 1) : d161795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d161795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d161795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d135431 q = 1) : d161796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d161796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d161796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d135431 q = 1) : d161797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d161797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d161797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d135431 q = 1) : d161798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d161798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d161798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32568 (p : Pattern) (ha : d115485 p = 1) (hb : d135431 p = 1) : d161804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d135431 q = 1) : d161762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d161762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32561 q ha hb
    | true =>
      simp only [d13658, d161762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32562 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d135431 q = 1) : d161763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d161763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d161763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d135431 q = 1) : d161764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d161764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d161764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d135431 q = 1) : d161765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d161765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d161765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d135431 q = 1) : d161769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d161769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32563 q ha hb
    | true =>
      simp only [d13668, d161769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32564 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d135431 q = 1) : d161770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d161770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d161770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d135431 q = 1) : d161771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d161771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d161771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d135431 q = 1) : d161793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d161793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32566 q ha hb
    | true =>
      simp only [d13704, d161793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32554 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d135431 q = 1) : d161794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d161794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d161794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d135431 q = 1) : d161799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d161799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32567 q ha hb
    | true =>
      simp only [d13745, d161799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d135431 q = 1) : d161800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d161800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d161800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d135431 q = 1) : d161801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d161801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d161801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d135431 q = 1) : d161802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d161802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d161802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d135431 q = 1) : d161803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d161803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d161803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115485 q = 1) (hb : d135431 q = 1) : d161804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d161804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d161804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32569 (p : Pattern) (ha : d13751 p = 1) (hb : d135431 p = 1) : d161805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d135431 q = 1) : d161738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d135431 q = 1) : d161739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d161739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d135431 q = 1) : d161760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d161760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d161760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13751 q = 1) (hb : d135431 q = 1) : d161805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d161805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13751, d161805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32570 (p : Pattern) (ha : d13752 p = 1) (hb : d135431 p = 1) : d139084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d135431 q = 1) : d139012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d135431 q = 1) : d139036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13752 q = 1) (hb : d135431 q = 1) : d139084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13752, d139084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13752, d139084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32571 (p : Pattern) (ha : d13757 p = 1) (hb : d135431 p = 1) : d161810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d135431 q = 1) : d161738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d161738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d135431 q = 1) : d161766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d161766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d161766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d135431 q = 1) : d161767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d161767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d161767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13757 q = 1) (hb : d135431 q = 1) : d161810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d161810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13757, d161810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32572 (p : Pattern) (ha : d13758 p = 1) (hb : d135431 p = 1) : d139090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d135431 q = 1) : d139011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d135431 q = 1) : d139045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d135431 q = 1) : d139046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13758 q = 1) (hb : d135431 q = 1) : d139090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13758, d139090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13758, d139090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32573 (p : Pattern) (ha : d13762 p = 1) (hb : d135431 p = 1) : d161814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d135431 q = 1) : d161778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d161778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32565 q ha hb
    | true =>
      simp only [d13690, d161778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d135431 q = 1) : d161779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d161779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d161779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d135431 q = 1) : d161783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32553 q ha hb
    | true =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d135431 q = 1) : d161784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d135431 q = 1) : d161785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d161785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d161785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d135431 q = 1) : d161786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d161786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d161786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d135431 q = 1) : d161787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d161787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d161787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d135431 q = 1) : d161814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d161814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d161814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32574 (p : Pattern) (ha : d13763 p = 1) (hb : d135431 p = 1) : d161815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d135431 q = 1) : d161783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32553 q ha hb
    | true =>
      simp only [d13694, d161783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d135431 q = 1) : d161784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d161784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d135431 q = 1) : d139005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32546 q ha hb
    | true =>
      simp only [d13625, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d135431 q = 1) : d139006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d135431 q = 1) : d161789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d161789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d161789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d135431 q = 1) : d161790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d161790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d161790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d135431 q = 1) : d161791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d161791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d161791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13763 q = 1) (hb : d135431 q = 1) : d161815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d161815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13763, d161815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32575 (p : Pattern) (ha : d13769 p = 1) (hb : d135431 p = 1) : d161818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d135431 q = 1) : d161736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32545 q ha hb
    | true =>
      simp only [d13621, d161736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d135431 q = 1) : d161737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d161737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d135431 q = 1) : d161795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d161795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d161795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d135431 q = 1) : d161796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d161796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d161796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d135431 q = 1) : d161797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d161797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d161797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d135431 q = 1) : d161818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d161818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d161818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32576 (p : Pattern) (ha : d115490 p = 1) (hb : d135431 p = 1) : d161824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d135431 q = 1) : d161762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d161762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32561 q ha hb
    | true =>
      simp only [d13658, d161762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32562 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d135431 q = 1) : d161763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d161763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d161763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d135431 q = 1) : d161764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d161764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d161764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d135431 q = 1) : d161765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d161765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d161765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d135431 q = 1) : d161769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d161769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32563 q ha hb
    | true =>
      simp only [d13668, d161769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32564 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d135431 q = 1) : d161770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d161770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d161770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d135431 q = 1) : d161771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d161771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d161771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d135431 q = 1) : d161793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d161793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32566 q ha hb
    | true =>
      simp only [d13704, d161793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32554 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d135431 q = 1) : d161794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d161794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d161794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d135431 q = 1) : d161799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d161799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32567 q ha hb
    | true =>
      simp only [d13745, d161799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d135431 q = 1) : d161800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d161800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d161800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d135431 q = 1) : d161801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d161801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d161801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d135431 q = 1) : d161802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d161802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d161802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d135431 q = 1) : d161803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d161803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d161803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13753 q = 1) (hb : d135431 q = 1) : d161806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d161806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32569 q ha hb
    | true =>
      simp only [d13753, d161806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32570 q ha hb
  have h16 (q : Pattern) (ha : d13754 q = 1) (hb : d135431 q = 1) : d161807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d161807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d161807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13755 q = 1) (hb : d135431 q = 1) : d161808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d161808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13755, d161808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13756 q = 1) (hb : d135431 q = 1) : d161809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d161809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d161809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13759 q = 1) (hb : d135431 q = 1) : d161811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d161811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32571 q ha hb
    | true =>
      simp only [d13759, d161811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32572 q ha hb
  have h20 (q : Pattern) (ha : d13760 q = 1) (hb : d135431 q = 1) : d161812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d161812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d161812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13761 q = 1) (hb : d135431 q = 1) : d161813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d161813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13761, d161813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13764 q = 1) (hb : d135431 q = 1) : d161816 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d161816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32573 q ha hb
    | true =>
      simp only [d13764, d161816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32574 q ha hb
  have h23 (q : Pattern) (ha : d115486 q = 1) (hb : d135431 q = 1) : d161817 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d161817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115486, d161817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13770 q = 1) (hb : d135431 q = 1) : d161819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d161819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32575 q ha hb
    | true =>
      simp only [d13770, d161819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13771 q = 1) (hb : d135431 q = 1) : d161820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d161820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13771, d161820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115487 q = 1) (hb : d135431 q = 1) : d161821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d161821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115487, d161821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115488 q = 1) (hb : d135431 q = 1) : d161822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d161822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115488, d161822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115489 q = 1) (hb : d135431 q = 1) : d161823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d161823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115489, d161823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115490 q = 1) (hb : d135431 q = 1) : d161824 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d161824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115490, d161824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32577 (p : Pattern) (ha : d115497 p = 1) (hb : d135431 p = 1) : d161838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d135431 q = 1) : d161816 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d161816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32573 q ha hb
    | true =>
      simp only [d13764, d161816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32574 q ha hb
  have h2 (q : Pattern) (ha : d115486 q = 1) (hb : d135431 q = 1) : d161817 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d161817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115486, d161817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d135431 q = 1) : d161819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d161819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32575 q ha hb
    | true =>
      simp only [d13770, d161819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d135431 q = 1) : d161820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d161820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d161820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d135431 q = 1) : d161821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d161821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d161821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d135431 q = 1) : d161836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d161836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d161836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d135431 q = 1) : d161837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d161837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d161837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d135431 q = 1) : d161838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d161838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d161838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32578 (p : Pattern) (ha : d13832 p = 1) (hb : d135431 p = 1) : d161853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13809 q = 1) (hb : d94753 q = 1) : d13809 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13810 q = 1) (hb : d135431 q = 1) : d139131 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13810, d135431, d139131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13810, d135431, d139131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13811 q = 1) (hb : d135431 q = 1) : d139132 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13811, d139132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13811, d139132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13812 q = 1) (hb : d135431 q = 1) : d139133 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13812, d139133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13812, d139133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13809 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13822 q = 1) (hb : d94753 q = 1) : d13822 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13823 q = 1) (hb : d135431 q = 1) : d161844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13823, d135431, d161844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13823, d135431, d161844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13824 q = 1) (hb : d135431 q = 1) : d161845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13824, d161845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13824, d161845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13825 q = 1) (hb : d135431 q = 1) : d161846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13825, d161846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13825, d161846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13826 q = 1) (hb : d135431 q = 1) : d161847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d161847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13826, d161847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6642 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13827 q = 1) (hb : d135431 q = 1) : d139134 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13827, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13828 q = 1) (hb : d135431 q = 1) : d139135 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13829 q = 1) (hb : d135431 q = 1) : d139136 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d6642 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6648 q = 1) (hb : d94753 q = 1) : d6648 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6649 q = 1) (hb : d135431 q = 1) : d161848 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d135431, d161848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d6649, d135431, d161848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6650 q = 1) (hb : d135431 q = 1) : d161849 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d161849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d161849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6651 q = 1) (hb : d135431 q = 1) : d161850 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d161850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d161850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13830 q = 1) (hb : d135431 q = 1) : d161851 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d161851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13830, d161851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13831 q = 1) (hb : d135431 q = 1) : d161852 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d161852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13831, d161852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13832 q = 1) (hb : d135431 q = 1) : d161853 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d161853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13832, d161853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32579 (p : Pattern) (ha : d13836 p = 1) (hb : d135431 p = 1) : d161858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6642 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13827 q = 1) (hb : d135431 q = 1) : d139134 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13827, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13828 q = 1) (hb : d135431 q = 1) : d139135 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13829 q = 1) (hb : d135431 q = 1) : d139136 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6642 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6648 q = 1) (hb : d94753 q = 1) : d6648 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6649 q = 1) (hb : d135431 q = 1) : d161848 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d135431, d161848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6649, d135431, d161848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6650 q = 1) (hb : d135431 q = 1) : d161849 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d161849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d161849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6651 q = 1) (hb : d135431 q = 1) : d161850 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d161850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d161850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13830 q = 1) (hb : d135431 q = 1) : d161851 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d161851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13830, d161851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6652 q = 1) (hb : d135431 q = 1) : d161856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d161856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6652, d161856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13835 q = 1) (hb : d135431 q = 1) : d161857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d161857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13835, d161857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13836 q = 1) (hb : d135431 q = 1) : d161858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d161858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13836, d161858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32580 (p : Pattern) (ha : d13842 p = 1) (hb : d135431 p = 1) : d161864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d135431 q = 1) : d161854 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d161854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32578 q ha hb
    | true =>
      simp only [d13833, d161854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d135431 q = 1) : d161855 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d161855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d161855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d135431 q = 1) : d161859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d161859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32579 q ha hb
    | true =>
      simp only [d13837, d161859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d135431 q = 1) : d161860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d161860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d161860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d135431 q = 1) : d161861 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d161861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d161861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d135431 q = 1) : d161862 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d161862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d161862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d135431 q = 1) : d161863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d161863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d161863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d135431 q = 1) : d161864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d161864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d161864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32581 (p : Pattern) (ha : d13855 p = 1) (hb : d135431 p = 1) : d161868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d135431 q = 1) : d161859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d161859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32579 q ha hb
    | true =>
      simp only [d13837, d161859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d135431 q = 1) : d161860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d161860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d161860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d135431 q = 1) : d139157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32558 q ha hb
    | true =>
      simp only [d13850, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d135431 q = 1) : d139158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13852 q = 1) (hb : d135431 q = 1) : d161865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d161865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d161865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13853 q = 1) (hb : d135431 q = 1) : d161866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d161866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13853, d161866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13854 q = 1) (hb : d135431 q = 1) : d161867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d161867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13854, d161867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13855 q = 1) (hb : d135431 q = 1) : d161868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d161868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13855, d161868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32582 (p : Pattern) (ha : d13896 p = 1) (hb : d135431 p = 1) : d161872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6642 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13827 q = 1) (hb : d135431 q = 1) : d139134 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13827, d135431, d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13828 q = 1) (hb : d135431 q = 1) : d139135 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13829 q = 1) (hb : d135431 q = 1) : d139136 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6642 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6648 q = 1) (hb : d94753 q = 1) : d6648 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6649 q = 1) (hb : d135431 q = 1) : d161848 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d135431, d161848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6649, d135431, d161848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6650 q = 1) (hb : d135431 q = 1) : d161849 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d161849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d161849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6651 q = 1) (hb : d135431 q = 1) : d161850 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d161850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d161850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13830 q = 1) (hb : d135431 q = 1) : d161851 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d161851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13830, d161851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13843 q = 1) (hb : d94753 q = 1) : d13843 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13844 q = 1) (hb : d135431 q = 1) : d139138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13844, d135431, d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13845 q = 1) (hb : d135431 q = 1) : d139139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13846 q = 1) (hb : d135431 q = 1) : d139140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13847 q = 1) (hb : d135431 q = 1) : d139146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13847, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d13895 q = 1) (hb : d135431 q = 1) : d161871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d161871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13895, d161871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13896 q = 1) (hb : d135431 q = 1) : d161872 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d161872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13896, d161872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro32583 (p : Pattern) (ha : d13902 p = 1) (hb : d135431 p = 1) : d161878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d135431 q = 1) : d161873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d161873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32582 q ha hb
    | true =>
      simp only [d13897, d161873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d135431 q = 1) : d161874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d161874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d161874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d135431 q = 1) : d161875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d161875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d161875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d135431 q = 1) : d161876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d161876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d161876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d135431 q = 1) : d161877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d161877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d161877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d135431 q = 1) : d161878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d161878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d161878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32584 (p : Pattern) (ha : d115507 p = 1) (hb : d135431 p = 1) : d161884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d135431 q = 1) : d161869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d161869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32580 q ha hb
    | true =>
      simp only [d13856, d161869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32581 q ha hb
  have h2 (q : Pattern) (ha : d115503 q = 1) (hb : d135431 q = 1) : d161870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d161870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115503, d161870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d135431 q = 1) : d161879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d161879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32583 q ha hb
    | true =>
      simp only [d13903, d161879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d135431 q = 1) : d161880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d161880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d161880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d135431 q = 1) : d161881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d161881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d161881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d135431 q = 1) : d161882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d161882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d161882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d135431 q = 1) : d161883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d161883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d161883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d135431 q = 1) : d161884 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d161884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d161884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32585 (p : Pattern) (ha : d115513 p = 1) (hb : d135431 p = 1) : d161890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d135431 q = 1) : d161748 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d161748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d161748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32549 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d135431 q = 1) : d161749 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d161749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d161749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d135431 q = 1) : d161757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d161757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32549 q ha hb
    | true =>
      simp only [d13651, d161757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32552 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d135431 q = 1) : d161758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d161758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d161758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d135431 q = 1) : d161759 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d161759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d161759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115491 q = 1) (hb : d135431 q = 1) : d161825 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d161825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32568 q ha hb
    | true =>
      simp only [d115491, d161825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32576 q ha hb
  have h7 (q : Pattern) (ha : d13794 q = 1) (hb : d135431 q = 1) : d161832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d161832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32555 q ha hb
    | true =>
      simp only [d13794, d161832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32556 q ha hb
  have h8 (q : Pattern) (ha : d115492 q = 1) (hb : d135431 q = 1) : d161833 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d161833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d161833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115493 q = 1) (hb : d135431 q = 1) : d161834 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d161834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115493, d161834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115494 q = 1) (hb : d135431 q = 1) : d161835 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d161835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115494, d161835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115498 q = 1) (hb : d135431 q = 1) : d161839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d161839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115498, d161839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32577 q ha hb
  have h12 (q : Pattern) (ha : d13803 q = 1) (hb : d135431 q = 1) : d139126 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, d139126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13803, d139126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32557 q ha hb
  have h13 (q : Pattern) (ha : d115499 q = 1) (hb : d135431 q = 1) : d161840 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d161840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115499, d161840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115500 q = 1) (hb : d135431 q = 1) : d161841 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d161841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115500, d161841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115501 q = 1) (hb : d135431 q = 1) : d161842 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d161842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115501, d161842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115502 q = 1) (hb : d135431 q = 1) : d161843 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d161843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115502, d161843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115508 q = 1) (hb : d135431 q = 1) : d161885 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d161885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115508, d161885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32584 q ha hb
  have h18 (q : Pattern) (ha : d13920 q = 1) (hb : d135431 q = 1) : d139194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, d139194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13920, d139194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32560 q ha hb
  have h19 (q : Pattern) (ha : d115509 q = 1) (hb : d135431 q = 1) : d161886 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d161886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115509, d161886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115510 q = 1) (hb : d135431 q = 1) : d161887 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d161887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115510, d161887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115511 q = 1) (hb : d135431 q = 1) : d161888 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d161888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115511, d161888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115512 q = 1) (hb : d135431 q = 1) : d161889 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d161889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115512, d161889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115513 q = 1) (hb : d135431 q = 1) : d161890 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d161890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115513, d161890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32586 (p : Pattern) (ha : d115519 p = 1) (hb : d135431 p = 1) : d161896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d135431 q = 1) : d161891 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d161891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d161891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32585 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d135431 q = 1) : d161892 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d161892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d161892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d135431 q = 1) : d161893 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d161893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d161893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d135431 q = 1) : d161894 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d161894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d161894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d135431 q = 1) : d161895 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d161895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d161895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d135431 q = 1) : d161896 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d161896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d161896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32587 (p : Pattern) (ha : d115525 p = 1) (hb : d135431 p = 1) : d161902 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d135431 q = 1) : d161304 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d161304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32384 q ha hb
    | true =>
      simp only [d115354, d161304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32422 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d135431 q = 1) : d161387 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d161387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d161387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32460 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d135431 q = 1) : d161388 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d161388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d161388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d135431 q = 1) : d161556 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d161556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d161556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32502 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d135431 q = 1) : d161557 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d161557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d161557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d135431 q = 1) : d161558 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d161558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d161558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d135431 q = 1) : d161726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d161726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d161726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32544 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d135431 q = 1) : d161727 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d161727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d161727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d135431 q = 1) : d161728 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d161728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d161728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d135431 q = 1) : d161729 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d161729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d161729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d135431 q = 1) : d161897 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d161897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d161897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32586 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d135431 q = 1) : d161898 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d161898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d161898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d135431 q = 1) : d161899 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d161899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d161899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d135431 q = 1) : d161900 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d161900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d161900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d135431 q = 1) : d161901 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d161901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d161901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d135431 q = 1) : d161902 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d161902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d161902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro32588 (p : Pattern) (ha : d115531 p = 1) (hb : d135431 p = 1) : d161908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d135431 q = 1) : d161903 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d161903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32587 q ha hb
    | true =>
      simp only [d115526, d161903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d135431 q = 1) : d161904 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d161904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d161904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d135431 q = 1) : d161905 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d161905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d161905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d135431 q = 1) : d161906 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d161906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d161906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d135431 q = 1) : d161907 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d161907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d161907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d135431 q = 1) : d161908 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d161908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d161908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32589 (p : Pattern) (ha : d115537 p = 1) (hb : d135431 p = 1) : d161914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d135431 q = 1) : d161909 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d161909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32588 q ha hb
    | true =>
      simp only [d115532, d161909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d135431 q = 1) : d161910 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d161910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d161910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d135431 q = 1) : d161911 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d161911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d161911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d135431 q = 1) : d161912 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d161912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d161912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d135431 q = 1) : d161913 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d161913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d161913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d135431 q = 1) : d161914 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d161914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d161914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32590 (p : Pattern) (ha : d115543 p = 1) (hb : d135431 p = 1) : d161920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d135431 q = 1) : d161915 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d161915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32589 q ha hb
    | true =>
      simp only [d115538, d161915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d135431 q = 1) : d161916 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d161916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d161916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d135431 q = 1) : d161917 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d161917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d161917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d135431 q = 1) : d161918 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d161918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d161918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d135431 q = 1) : d161919 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d161919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d161919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d135431 q = 1) : d161920 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d161920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d161920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32591 (p : Pattern) (ha : d115549 p = 1) (hb : d135432 p = 1) : d161926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d135431 q = 1) : d161921 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d161921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32590 q ha hb
    | true =>
      simp only [d115544, d161921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d135431 q = 1) : d161922 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d161922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d161922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115546 q = 1) (hb : d135432 q = 1) : d161923 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d135432, d161923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d135432, d161923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115547 q = 1) (hb : d135432 q = 1) : d161924 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d161924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115547, d161924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115548 q = 1) (hb : d135432 q = 1) : d161925 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d161925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115548, d161925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d115549 q = 1) (hb : d135432 q = 1) : d161926 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d161926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115549, d161926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro32592 (p : Pattern) (ha : d115555 p = 1) (hb : d135432 p = 1) : d161932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d135432 q = 1) : d161927 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d161927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32591 q ha hb
    | true =>
      simp only [d115550, d161927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d135432 q = 1) : d161928 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d161928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d161928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d135432 q = 1) : d161929 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d161929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d161929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d135432 q = 1) : d161930 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d161930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d161930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d135432 q = 1) : d161931 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d161931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d161931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d135432 q = 1) : d161932 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d161932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d161932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32593 (p : Pattern) (ha : d115561 p = 1) (hb : d135432 p = 1) : d161938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d135432 q = 1) : d161933 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d161933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32592 q ha hb
    | true =>
      simp only [d115556, d161933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d135432 q = 1) : d161934 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d161934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d161934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d135432 q = 1) : d161935 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d161935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d161935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d135432 q = 1) : d161936 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d161936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d161936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d135432 q = 1) : d161937 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d161937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d161937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d135432 q = 1) : d161938 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d161938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d161938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32594 (p : Pattern) (ha : d115567 p = 1) (hb : d135432 p = 1) : d161944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d135432 q = 1) : d161939 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d161939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32593 q ha hb
    | true =>
      simp only [d115562, d161939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d135432 q = 1) : d161940 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d161940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d161940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d135432 q = 1) : d161941 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d161941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d161941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d135432 q = 1) : d161942 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d161942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d161942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d135432 q = 1) : d161943 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d161943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d161943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d135432 q = 1) : d161944 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d161944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d161944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32595 (p : Pattern) (ha : d1 p = 1) (hb : d161944 p = 1) : d161944 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d161944 q = 1) : d161944 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro32596 (p : Pattern) (ha : d135431 p = 1) (hb : d150329 p = 1) : d138288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32357 q ha hb
    | true =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h2 (q : Pattern) (ha : d12292 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12293 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12293, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12294 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12295 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150329 q = 1) : d138288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150329, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32597 (p : Pattern) (ha : d135431 p = 1) (hb : d150339 p = 1) : d138323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32361 q ha hb
    | true =>
      simp only [d12268, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150335 q = 1) : d138319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150335, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150336 q = 1) : d138320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150336, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150337 q = 1) : d138321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150337, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150338 q = 1) : d138322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150338, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150339 q = 1) : d138323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150339, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32598 (p : Pattern) (ha : d135431 p = 1) (hb : d150345 p = 1) : d139264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d135431 q = 1) : d138115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32364 q ha hb
    | true =>
      simp only [d12297, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32365 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d135431 q = 1) : d138116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150327 q = 1) : d139254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d139254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150327, d139254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150328 q = 1) : d139255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d139255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150328, d139255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150330 q = 1) : d138289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150330, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32596 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150331 q = 1) : d139256 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d139256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d139256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150332 q = 1) : d139257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d139257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d139257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150333 q = 1) : d139258 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d139258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d139258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150334 q = 1) : d139259 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d139259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d139259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150340 q = 1) : d138324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150340, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32597 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150341 q = 1) : d139260 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d139260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d139260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150342 q = 1) : d139261 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d139261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d139261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150343 q = 1) : d139262 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d139262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d139262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150344 q = 1) : d139263 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d139263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d139263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150345 q = 1) : d139264 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d139264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d139264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32599 (p : Pattern) (ha : d135431 p = 1) (hb : d150351 p = 1) : d139270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24581 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150346 q = 1) : d139265 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d139265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150346, d139265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32598 q ha hb
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150347 q = 1) : d139266 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d139266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150347, d139266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150348 q = 1) : d139267 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d139267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150348, d139267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150349 q = 1) : d139268 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d139268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150349, d139268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150350 q = 1) : d139269 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d139269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150350, d139269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150351 q = 1) : d139270 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d139270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150351, d139270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32600 (p : Pattern) (ha : d135431 p = 1) (hb : d150354 p = 1) : d139273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32390 q ha hb
    | true =>
      simp only [d12463, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32391 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d135431 q = 1) : d138215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d135431 q = 1) : d138216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d135431 q = 1) : d138217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d135431 q = 1) : d138218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150354 q = 1) : d139273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d139273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150354, d139273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32601 (p : Pattern) (ha : d135431 p = 1) (hb : d150365 p = 1) : d139283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150360 q = 1) : d138190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32418 q hb ha
    | true =>
      simp only [d150360, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32397 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150361 q = 1) : d139279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d139279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150361, d139279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150362 q = 1) : d139280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d139280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d139280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150363 q = 1) : d139281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d139281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150363, d139281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150364 q = 1) : d139282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d139282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150364, d139282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150365 q = 1) : d139283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d139283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150365, d139283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32602 (p : Pattern) (ha : d135431 p = 1) (hb : d150371 p = 1) : d139289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d135431 q = 1) : d138220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32389 q ha hb
    | true =>
      simp only [d12469, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32392 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d135431 q = 1) : d138221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150352 q = 1) : d139271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d139271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150352, d139271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150353 q = 1) : d139272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d139272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150353, d139272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150355 q = 1) : d139274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d139274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150355, d139274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32600 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150356 q = 1) : d139275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d139275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d139275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150357 q = 1) : d139276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d139276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d139276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150358 q = 1) : d139277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d139277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d139277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150359 q = 1) : d139278 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d139278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d139278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150366 q = 1) : d139284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d139284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150366, d139284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32601 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150367 q = 1) : d139285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d139285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d139285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150368 q = 1) : d139286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d139286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d139286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150369 q = 1) : d139287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d139287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d139287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150370 q = 1) : d139288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d139288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d139288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150371 q = 1) : d139289 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d139289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d139289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32603 (p : Pattern) (ha : d135431 p = 1) (hb : d150377 p = 1) : d139295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150372 q = 1) : d139290 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d139290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150372, d139290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32602 q ha hb
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150373 q = 1) : d139291 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d139291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150373, d139291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150374 q = 1) : d139292 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d139292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150374, d139292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150375 q = 1) : d139293 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d139293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150375, d139293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150376 q = 1) : d139294 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d139294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150376, d139294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150377 q = 1) : d139295 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d139295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150377, d139295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32604 (p : Pattern) (ha : d135431 p = 1) (hb : d150381 p = 1) : d139299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d135431 q = 1) : d138371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32428 q ha hb
    | true =>
      simp only [d12718, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32429 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d135431 q = 1) : d138372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d135431 q = 1) : d138373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d135431 q = 1) : d138374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d135431 q = 1) : d138375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150381 q = 1) : d139299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d139299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150381, d139299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32605 (p : Pattern) (ha : d135431 p = 1) (hb : d150392 p = 1) : d139310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150387 q = 1) : d139305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d139305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32456 q hb ha
    | true =>
      simp only [d150387, d139305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32435 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150388 q = 1) : d139306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d139306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150388, d139306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150389 q = 1) : d139307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d139307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d139307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150390 q = 1) : d139308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d139308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150390, d139308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150391 q = 1) : d139309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d139309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150391, d139309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150392 q = 1) : d139310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d139310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150392, d139310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32606 (p : Pattern) (ha : d135431 p = 1) (hb : d150398 p = 1) : d139316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d135431 q = 1) : d138377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32427 q ha hb
    | true =>
      simp only [d12724, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32430 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d135431 q = 1) : d138378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150379 q = 1) : d139297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d139297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150379, d139297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150380 q = 1) : d139298 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d139298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150380, d139298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150382 q = 1) : d139300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d139300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150382, d139300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32604 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150383 q = 1) : d139301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d139301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d139301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150384 q = 1) : d139302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d139302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d139302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150385 q = 1) : d139303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d139303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d139303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150386 q = 1) : d139304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d139304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d139304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150393 q = 1) : d139311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d139311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150393, d139311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32605 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150394 q = 1) : d139312 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d139312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d139312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150395 q = 1) : d139313 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d139313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d139313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150396 q = 1) : d139314 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d139314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d139314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150397 q = 1) : d139315 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d139315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d139315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150398 q = 1) : d139316 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d139316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d139316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32607 (p : Pattern) (ha : d135431 p = 1) (hb : d150404 p = 1) : d139322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150399 q = 1) : d139317 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d139317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150399, d139317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32606 q ha hb
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150400 q = 1) : d139318 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d139318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150400, d139318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150401 q = 1) : d139319 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d139319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150401, d139319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150402 q = 1) : d139320 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d139320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150402, d139320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150403 q = 1) : d139321 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d139321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150403, d139321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150404 q = 1) : d139322 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d139322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150404, d139322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32608 (p : Pattern) (ha : d135431 p = 1) (hb : d150409 p = 1) : d161947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d135431 q = 1) : d161410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d161410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32466 q ha hb
    | true =>
      simp only [d12992, d161410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32467 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d135431 q = 1) : d161411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d161411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d161411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d135431 q = 1) : d161412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d161412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d161412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d135431 q = 1) : d161413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d161413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d161413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d135431 q = 1) : d161414 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d161414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d161414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150409 q = 1) : d161947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d161947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150409, d161947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32609 (p : Pattern) (ha : d135431 p = 1) (hb : d150418 p = 1) : d161956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d135431 q = 1) : d161532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d161532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32498 q ha hb
    | true =>
      simp only [d13244, d161532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d135431 q = 1) : d161533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d161533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d161533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d135431 q = 1) : d138720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32474 q ha hb
    | true =>
      simp only [d13197, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d135431 q = 1) : d138721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150415 q = 1) : d161953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d161953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150415, d161953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150416 q = 1) : d161954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d161954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d161954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150417 q = 1) : d161955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d161955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d161955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150418 q = 1) : d161956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d161956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d161956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32610 (p : Pattern) (ha : d135431 p = 1) (hb : d150424 p = 1) : d161962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150419 q = 1) : d161957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d161957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32609 q ha hb
    | true =>
      simp only [d150419, d161957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32475 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150420 q = 1) : d161958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d161958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150420, d161958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150421 q = 1) : d161959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d161959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d161959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150422 q = 1) : d161960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d161960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150422, d161960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150423 q = 1) : d161961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d161961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150423, d161961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150424 q = 1) : d161962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d161962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150424, d161962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32611 (p : Pattern) (ha : d135431 p = 1) (hb : d150430 p = 1) : d161968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d135431 q = 1) : d161416 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d161416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32465 q ha hb
    | true =>
      simp only [d12998, d161416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32468 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d135431 q = 1) : d161417 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d161417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d161417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150407 q = 1) : d161945 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d161945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150407, d161945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150408 q = 1) : d161946 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d161946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150408, d161946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150410 q = 1) : d161948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d161948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150410, d161948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32608 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150411 q = 1) : d161949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d161949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d161949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150412 q = 1) : d161950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d161950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d161950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150413 q = 1) : d161951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d161951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d161951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150414 q = 1) : d161952 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d161952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d161952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150425 q = 1) : d161963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d161963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150425, d161963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32610 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150426 q = 1) : d161964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d161964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d161964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150427 q = 1) : d161965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d161965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d161965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150428 q = 1) : d161966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d161966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d161966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150429 q = 1) : d161967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d161967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d161967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150430 q = 1) : d161968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d161968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d161968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32612 (p : Pattern) (ha : d135431 p = 1) (hb : d150436 p = 1) : d161974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150431 q = 1) : d161969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d161969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150431, d161969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32611 q ha hb
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150432 q = 1) : d161970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d161970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150432, d161970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150433 q = 1) : d161971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d161971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150433, d161971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150434 q = 1) : d161972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d161972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150434, d161972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150435 q = 1) : d161973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d161973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150435, d161973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150436 q = 1) : d161974 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d161974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150436, d161974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32613 (p : Pattern) (ha : d135431 p = 1) (hb : d150442 p = 1) : d161980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d135431 q = 1) : d161580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d161580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32508 q ha hb
    | true =>
      simp only [d13318, d161580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32509 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d135431 q = 1) : d161581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d161581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d161581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d135431 q = 1) : d161582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d161582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d161582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d135431 q = 1) : d161583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d161583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d161583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d135431 q = 1) : d161584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d161584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d161584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150442 q = 1) : d161980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d161980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150442, d161980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32614 (p : Pattern) (ha : d135431 p = 1) (hb : d150451 p = 1) : d161989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d135431 q = 1) : d161702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d161702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32540 q ha hb
    | true =>
      simp only [d13570, d161702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d135431 q = 1) : d161703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d161703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d161703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d135431 q = 1) : d138938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32516 q ha hb
    | true =>
      simp only [d13523, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d135431 q = 1) : d138939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150448 q = 1) : d161986 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d161986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150448, d161986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150449 q = 1) : d161987 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d161987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d161987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150450 q = 1) : d161988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d161988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d161988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150451 q = 1) : d161989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d161989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d161989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32615 (p : Pattern) (ha : d135431 p = 1) (hb : d150457 p = 1) : d161995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150452 q = 1) : d161990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d161990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32614 q ha hb
    | true =>
      simp only [d150452, d161990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32517 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150453 q = 1) : d161991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d161991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150453, d161991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150454 q = 1) : d161992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d161992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d161992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150455 q = 1) : d161993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d161993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150455, d161993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150456 q = 1) : d161994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d161994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150456, d161994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150457 q = 1) : d161995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d161995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150457, d161995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32616 (p : Pattern) (ha : d135431 p = 1) (hb : d150463 p = 1) : d162001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d135431 q = 1) : d161586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d161586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32507 q ha hb
    | true =>
      simp only [d13324, d161586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32510 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d135431 q = 1) : d161587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d161587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d161587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150440 q = 1) : d161978 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d161978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150440, d161978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150441 q = 1) : d161979 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d161979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150441, d161979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150443 q = 1) : d161981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d161981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150443, d161981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32613 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150444 q = 1) : d161982 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d161982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d161982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150445 q = 1) : d161983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d161983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d161983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150446 q = 1) : d161984 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d161984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d161984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150447 q = 1) : d161985 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d161985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d161985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150458 q = 1) : d161996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d161996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150458, d161996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32615 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150459 q = 1) : d161997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d161997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d161997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150460 q = 1) : d161998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d161998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d161998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150461 q = 1) : d161999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d161999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d161999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150462 q = 1) : d162000 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d162000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d162000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150463 q = 1) : d162001 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d162001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d162001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32617 (p : Pattern) (ha : d135431 p = 1) (hb : d150469 p = 1) : d162007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150464 q = 1) : d162002 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d162002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150464, d162002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32616 q ha hb
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150465 q = 1) : d162003 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d162003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150465, d162003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150466 q = 1) : d162004 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d162004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150466, d162004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150467 q = 1) : d162005 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d162005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150467, d162005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150468 q = 1) : d162006 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d162006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150468, d162006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150469 q = 1) : d162007 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d162007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150469, d162007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32618 (p : Pattern) (ha : d135431 p = 1) (hb : d150476 p = 1) : d162014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d135431 q = 1) : d161751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d161751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32550 q ha hb
    | true =>
      simp only [d13645, d161751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32551 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d135431 q = 1) : d161752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d161752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d161752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d135431 q = 1) : d161753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d161753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d161753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d135431 q = 1) : d161754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d161754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d161754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d135431 q = 1) : d161755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d161755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d161755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150476 q = 1) : d162014 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d162014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150476, d162014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32619 (p : Pattern) (ha : d135431 p = 1) (hb : d150485 p = 1) : d162023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d135431 q = 1) : d161873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d161873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32582 q ha hb
    | true =>
      simp only [d13897, d161873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d135431 q = 1) : d161874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d161874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d161874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d135431 q = 1) : d139157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32558 q ha hb
    | true =>
      simp only [d13850, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d135431 q = 1) : d139158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150482 q = 1) : d162020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d162020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150482, d162020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150483 q = 1) : d162021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d162021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d162021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150484 q = 1) : d162022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d162022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d162022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150485 q = 1) : d162023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d162023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d162023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32620 (p : Pattern) (ha : d135431 p = 1) (hb : d150491 p = 1) : d162029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150486 q = 1) : d162024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d162024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32619 q ha hb
    | true =>
      simp only [d150486, d162024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32559 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150487 q = 1) : d162025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d162025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150487, d162025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150488 q = 1) : d162026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d162026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d162026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150489 q = 1) : d162027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d162027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150489, d162027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150490 q = 1) : d162028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d162028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150490, d162028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150491 q = 1) : d162029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d162029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150491, d162029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32621 (p : Pattern) (ha : d135431 p = 1) (hb : d150497 p = 1) : d162035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d135431 q = 1) : d161757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d161757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32549 q ha hb
    | true =>
      simp only [d13651, d161757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32552 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d135431 q = 1) : d161758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d161758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d161758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150474 q = 1) : d162012 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d162012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150474, d162012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150475 q = 1) : d162013 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d162013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150475, d162013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150477 q = 1) : d162015 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d162015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150477, d162015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32618 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150478 q = 1) : d162016 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d162016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d162016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150479 q = 1) : d162017 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d162017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d162017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150480 q = 1) : d162018 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d162018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d162018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150481 q = 1) : d162019 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d162019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d162019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150492 q = 1) : d162030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d162030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150492, d162030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32620 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150493 q = 1) : d162031 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d162031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d162031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150494 q = 1) : d162032 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d162032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d162032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150495 q = 1) : d162033 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d162033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d162033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150496 q = 1) : d162034 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d162034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d162034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150497 q = 1) : d162035 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d162035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d162035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32622 (p : Pattern) (ha : d135431 p = 1) (hb : d150503 p = 1) : d162041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150498 q = 1) : d162036 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d162036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150498, d162036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32621 q ha hb
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150499 q = 1) : d162037 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d162037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150499, d162037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150500 q = 1) : d162038 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d162038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150500, d162038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150501 q = 1) : d162039 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d162039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150501, d162039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150502 q = 1) : d162040 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d162040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150502, d162040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150503 q = 1) : d162041 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d162041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150503, d162041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32623 (p : Pattern) (ha : d135431 p = 1) (hb : d150509 p = 1) : d162047 p = 1 := by
  have h0 (q : Pattern) (ha : d135431 q = 1) (hb : d150378 q = 1) : d139296 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d139296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32599 q ha hb
    | true =>
      simp only [d150378, d139296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32603 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150405 q = 1) : d139323 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d139323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150405, d139323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32607 q ha hb
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150406 q = 1) : d139324 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d139324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d139324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150437 q = 1) : d161975 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d161975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150437, d161975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32612 q ha hb
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150438 q = 1) : d161976 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d161976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150438, d161976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150439 q = 1) : d161977 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d161977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d161977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d135431 q = 1) (hb : d150470 q = 1) : d162008 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d162008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150470, d162008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32617 q ha hb
  have h8 (q : Pattern) (ha : d135431 q = 1) (hb : d150471 q = 1) : d162009 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d162009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150471, d162009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d135431 q = 1) (hb : d150472 q = 1) : d162010 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d162010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150472, d162010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135431 q = 1) (hb : d150473 q = 1) : d162011 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d162011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d162011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d135431 q = 1) (hb : d150504 q = 1) : d162042 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d162042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150504, d162042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32622 q ha hb
  have h12 (q : Pattern) (ha : d135431 q = 1) (hb : d150505 q = 1) : d162043 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d162043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150505, d162043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d135431 q = 1) (hb : d150506 q = 1) : d162044 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d162044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150506, d162044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d135431 q = 1) (hb : d150507 q = 1) : d162045 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d162045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150507, d162045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d135431 q = 1) (hb : d150508 q = 1) : d162046 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d162046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d162046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d135431 q = 1) (hb : d150509 q = 1) : d162047 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d162047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d162047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro32624 (p : Pattern) (ha : d135431 p = 1) (hb : d150515 p = 1) : d162053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150510 q = 1) : d162048 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d162048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32623 q ha hb
    | true =>
      simp only [d150510, d162048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150511 q = 1) : d162049 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d162049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d162049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150512 q = 1) : d162050 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d162050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d162050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150513 q = 1) : d162051 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d162051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d162051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150514 q = 1) : d162052 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d162052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d162052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150515 q = 1) : d162053 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d162053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d162053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32625 (p : Pattern) (ha : d135431 p = 1) (hb : d150521 p = 1) : d162059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150516 q = 1) : d162054 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d162054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32624 q ha hb
    | true =>
      simp only [d150516, d162054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150517 q = 1) : d162055 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d162055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d162055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150518 q = 1) : d162056 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d162056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d162056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150519 q = 1) : d162057 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d162057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d162057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150520 q = 1) : d162058 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d162058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d162058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150521 q = 1) : d162059 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d162059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d162059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32626 (p : Pattern) (ha : d135431 p = 1) (hb : d150527 p = 1) : d162065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150522 q = 1) : d162060 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d162060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32625 q ha hb
    | true =>
      simp only [d150522, d162060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150523 q = 1) : d162061 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d162061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d162061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d135431 q = 1) (hb : d150524 q = 1) : d162062 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d162062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d162062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135431 q = 1) (hb : d150525 q = 1) : d162063 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d162063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d162063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d135431 q = 1) (hb : d150526 q = 1) : d162064 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d162064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d162064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d135431 q = 1) (hb : d150527 q = 1) : d162065 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d162065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d162065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32627 (p : Pattern) (ha : d135432 p = 1) (hb : d150533 p = 1) : d162071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135431 q = 1) (hb : d150528 q = 1) : d162066 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d162066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32626 q ha hb
    | true =>
      simp only [d150528, d162066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135431 q = 1) (hb : d150529 q = 1) : d162067 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d162067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d162067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d135432 q = 1) (hb : d150530 q = 1) : d162068 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d135432, d150530, d162068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135432, d150530, d162068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d135432 q = 1) (hb : d150531 q = 1) : d162069 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d162069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150531, d162069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d135432 q = 1) (hb : d150532 q = 1) : d162070 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d162070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150532, d162070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d135432 q = 1) (hb : d150533 q = 1) : d162071 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d162071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150533, d162071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro32628 (p : Pattern) (ha : d135432 p = 1) (hb : d150539 p = 1) : d162077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135432 q = 1) (hb : d150534 q = 1) : d162072 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d162072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32627 q ha hb
    | true =>
      simp only [d150534, d162072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135432 q = 1) (hb : d150535 q = 1) : d162073 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d162073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d162073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d135432 q = 1) (hb : d150536 q = 1) : d162074 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d162074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d162074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135432 q = 1) (hb : d150537 q = 1) : d162075 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d162075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d162075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d135432 q = 1) (hb : d150538 q = 1) : d162076 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d162076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d162076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d135432 q = 1) (hb : d150539 q = 1) : d162077 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d162077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d162077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32629 (p : Pattern) (ha : d135432 p = 1) (hb : d150545 p = 1) : d162083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135432 q = 1) (hb : d150540 q = 1) : d162078 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d162078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32628 q ha hb
    | true =>
      simp only [d150540, d162078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135432 q = 1) (hb : d150541 q = 1) : d162079 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d162079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d162079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d135432 q = 1) (hb : d150542 q = 1) : d162080 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d162080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d162080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135432 q = 1) (hb : d150543 q = 1) : d162081 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d162081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d162081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d135432 q = 1) (hb : d150544 q = 1) : d162082 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d162082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d162082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d135432 q = 1) (hb : d150545 q = 1) : d162083 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d162083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d162083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32630 (p : Pattern) (ha : d135432 p = 1) (hb : d150551 p = 1) : d162089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d135432 q = 1) (hb : d150546 q = 1) : d162084 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d162084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32629 q ha hb
    | true =>
      simp only [d150546, d162084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d135432 q = 1) (hb : d150547 q = 1) : d162085 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d162085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d162085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d135432 q = 1) (hb : d150548 q = 1) : d162086 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d162086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d162086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d135432 q = 1) (hb : d150549 q = 1) : d162087 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d162087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d162087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d135432 q = 1) (hb : d150550 q = 1) : d162088 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d162088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d162088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d135432 q = 1) (hb : d150551 q = 1) : d162089 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d162089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d162089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32631 (p : Pattern) (ha : d1 p = 1) (hb : d162089 p = 1) : d162089 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d162089 q = 1) : d162089 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro32632 (p : Pattern) (ha : d0 p = 1) (hb : d162089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162089 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro32633 (p : Pattern) (ha : d12227 p = 1) (hb : d112688 p = 1) : d114101 p = 1 := by
  have h0 (q : Pattern) (ha : d12225 q = 1) (hb : d112687 q = 1) : d12225 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12226 q = 1) (hb : d112688 q = 1) : d114100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d112688, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12226, d112688, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12227 q = 1) (hb : d112688 q = 1) : d114101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12227, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro32634 (p : Pattern) (ha : d12233 p = 1) (hb : d112688 p = 1) : d114107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d112688 q = 1) : d114106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12233 q = 1) (hb : d112688 q = 1) : d114107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32635 (p : Pattern) (ha : d112688 p = 1) (hb : d115242 p = 1) : d114113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d112688 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d112688 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12234 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
    | true =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115238 q = 1) : d114109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115238, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d112688 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115239 q = 1) : d114110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115240 q = 1) : d114111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115240, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115241 q = 1) : d114112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115241, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115242 q = 1) : d114113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115242, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32636 (p : Pattern) (ha : d12240 p = 1) (hb : d112688 p = 1) : d114114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d112688 q = 1) : d114106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12240 q = 1) (hb : d112688 q = 1) : d114114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12240, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32637 (p : Pattern) (ha : d112688 p = 1) (hb : d115247 p = 1) : d114120 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d112688 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d112688 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12234 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
    | true =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115238 q = 1) : d114109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115238, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d112688 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115239 q = 1) : d114110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115240 q = 1) : d114111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115240, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115241 q = 1) : d114112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115241, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d112688 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d112688 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12241 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32636 q ha hb
    | true =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115243 q = 1) : d114116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d115243, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d112688 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115244 q = 1) : d114117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115244, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115245 q = 1) : d114118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115245, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115246 q = 1) : d114119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115246, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d112688 q = 1) (hb : d115247 q = 1) : d114120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115247, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32638 (p : Pattern) (ha : d112688 p = 1) (hb : d115254 p = 1) : d114127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32636 q ha hb
    | true =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115243 q = 1) : d114116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115243, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d112688 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115244 q = 1) : d114117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115244, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115252 q = 1) : d114125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115252, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115253 q = 1) : d114126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115253, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115254 q = 1) : d114127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115254, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32639 (p : Pattern) (ha : d12261 p = 1) (hb : d112688 p = 1) : d114134 p = 1 := by
  have h0 (q : Pattern) (ha : d12259 q = 1) (hb : d112687 q = 1) : d12259 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12260 q = 1) (hb : d112688 q = 1) : d114133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d112688, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12260, d112688, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12261 q = 1) (hb : d112688 q = 1) : d114134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12261, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro32640 (p : Pattern) (ha : d12267 p = 1) (hb : d112688 p = 1) : d114140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d112688 q = 1) : d114135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32639 q ha hb
    | true =>
      simp only [d12262, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d112688 q = 1) : d114136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d112688 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12264 q = 1) (hb : d112688 q = 1) : d114137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12265 q = 1) (hb : d112688 q = 1) : d114138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12265, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12266 q = 1) (hb : d112688 q = 1) : d114139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12266, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12267 q = 1) (hb : d112688 q = 1) : d114140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12267, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32641 (p : Pattern) (ha : d112688 p = 1) (hb : d115264 p = 1) : d114146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d112688 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d112688 q = 1) : d114141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32640 q ha hb
    | true =>
      simp only [d12268, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115260 q = 1) : d114142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115260, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d112688 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115261 q = 1) : d114143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115261, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115262 q = 1) : d114144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115262, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115263 q = 1) : d114145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115263, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115264 q = 1) : d114146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115264, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32642 (p : Pattern) (ha : d112688 p = 1) (hb : d115270 p = 1) : d114152 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d112688 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115248 q = 1) : d114121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32635 q ha hb
    | true =>
      simp only [d115248, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32637 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d112688 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115249 q = 1) : d114122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115249, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115250 q = 1) : d114123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115250, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115251 q = 1) : d114124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115251, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115255 q = 1) : d114128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115255, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32638 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115256 q = 1) : d114129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115256, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115257 q = 1) : d114130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115257, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115258 q = 1) : d114131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115258, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115259 q = 1) : d114132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115259, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115265 q = 1) : d114147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115265, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32641 q ha hb
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d115266 q = 1) : d114148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115266, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115267 q = 1) : d114149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115267, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115268 q = 1) : d114150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115268, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115269 q = 1) : d114151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115269, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115270 q = 1) : d114152 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115270, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32643 (p : Pattern) (ha : d12289 p = 1) (hb : d112688 p = 1) : d114162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
    | true =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d112688 q = 1) : d114158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d112688 q = 1) : d114159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d112688 q = 1) : d114160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d112688 q = 1) : d114161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12289 q = 1) (hb : d112688 q = 1) : d114162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32644 (p : Pattern) (ha : d12296 p = 1) (hb : d112688 p = 1) : d114169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
    | true =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d112688 q = 1) : d114158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d112688 q = 1) : d114159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d112688 q = 1) : d114160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d112688 q = 1) : d114161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12241 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32636 q ha hb
    | true =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12292 q = 1) (hb : d112688 q = 1) : d114165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12293 q = 1) (hb : d112688 q = 1) : d114166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12293, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12294 q = 1) (hb : d112688 q = 1) : d114167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12295 q = 1) (hb : d112688 q = 1) : d114168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12296 q = 1) (hb : d112688 q = 1) : d114169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12296, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro32645 (p : Pattern) (ha : d12373 p = 1) (hb : d112688 p = 1) : d114226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
    | true =>
      simp only [d12234, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d112688 q = 1) : d114158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d112688 q = 1) : d114159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d112688 q = 1) : d114160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d112688 q = 1) : d114161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d112688 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12373 q = 1) (hb : d112688 q = 1) : d114226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12373, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32646 (p : Pattern) (ha : d12301 p = 1) (hb : d112688 p = 1) : d114174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d112688 q = 1) : d114173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12301 q = 1) (hb : d112688 q = 1) : d114174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32647 (p : Pattern) (ha : d12308 p = 1) (hb : d112688 p = 1) : d114181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d112688 q = 1) : d114179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d112688 q = 1) : d114180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12308 q = 1) (hb : d112688 q = 1) : d114181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32648 (p : Pattern) (ha : d12318 p = 1) (hb : d112688 p = 1) : d114187 p = 1 := by
  have h0 (q : Pattern) (ha : d12315 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4818 q = 1) (hb : d94753 q = 1) : d4818 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4819, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12316 q = 1) (hb : d112687 q = 1) : d114185 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d112687, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12316, d112687, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12225 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12317 q = 1) (hb : d112688 q = 1) : d114186 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d112688, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12317, d112688, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12318 q = 1) (hb : d112688 q = 1) : d114187 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12318, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32649 (p : Pattern) (ha : d12324 p = 1) (hb : d112688 p = 1) : d114193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32648 q ha hb
    | true =>
      simp only [d12319, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d112688 q = 1) : d114190 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d112688 q = 1) : d114191 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d112688 q = 1) : d114192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d112688 q = 1) : d114193 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32650 (p : Pattern) (ha : d12344 p = 1) (hb : d112688 p = 1) : d114199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d112688 q = 1) : d114196 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d112688 q = 1) : d114197 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d112688 q = 1) : d114198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d112688 q = 1) : d114199 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32651 (p : Pattern) (ha : d112688 p = 1) (hb : d115280 p = 1) : d114205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d112688 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d112688 q = 1) : d114175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32646 q ha hb
    | true =>
      simp only [d12302, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d112688 q = 1) : d114176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d112688 q = 1) : d114177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d112688 q = 1) : d114178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d112688 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d112688 q = 1) : d114182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32647 q ha hb
    | true =>
      simp only [d12309, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d112688 q = 1) : d114183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d112688 q = 1) : d114184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d112688 q = 1) : d114194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32649 q ha hb
    | true =>
      simp only [d12325, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115276 q = 1) : d114195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115276, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d112688 q = 1) : d114200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32650 q ha hb
    | true =>
      simp only [d12345, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d112688 q = 1) : d114201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115277 q = 1) : d114202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115278 q = 1) : d114203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115278, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115279 q = 1) : d114204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115279, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115280 q = 1) : d114205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115280, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32652 (p : Pattern) (ha : d12351 p = 1) (hb : d112688 p = 1) : d114206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d112688 q = 1) : d114173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12351 q = 1) (hb : d112688 q = 1) : d114206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12351, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32653 (p : Pattern) (ha : d12356 p = 1) (hb : d112688 p = 1) : d114211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d112688 q = 1) : d114179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d112688 q = 1) : d114180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12356 q = 1) (hb : d112688 q = 1) : d114211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12356, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32654 (p : Pattern) (ha : d12360 p = 1) (hb : d112688 p = 1) : d114215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32648 q ha hb
    | true =>
      simp only [d12319, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d112688 q = 1) : d114190 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d112688 q = 1) : d114191 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d112688 q = 1) : d114192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d112688 q = 1) : d114215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32655 (p : Pattern) (ha : d12365 p = 1) (hb : d112688 p = 1) : d114218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32633 q ha hb
    | true =>
      simp only [d12228, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d112688 q = 1) : d114196 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d112688 q = 1) : d114197 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d112688 q = 1) : d114198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d112688 q = 1) : d114218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32656 (p : Pattern) (ha : d112688 p = 1) (hb : d115285 p = 1) : d114224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d112688 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d112688 q = 1) : d114175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32646 q ha hb
    | true =>
      simp only [d12302, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d112688 q = 1) : d114176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d112688 q = 1) : d114177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d112688 q = 1) : d114178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d112688 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d112688 q = 1) : d114182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32647 q ha hb
    | true =>
      simp only [d12309, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d112688 q = 1) : d114183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d112688 q = 1) : d114184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d112688 q = 1) : d114194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32649 q ha hb
    | true =>
      simp only [d12325, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32634 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115276 q = 1) : d114195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115276, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d112688 q = 1) : d114200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32650 q ha hb
    | true =>
      simp only [d12345, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d112688 q = 1) : d114201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115277 q = 1) : d114202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115278 q = 1) : d114203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115278, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115279 q = 1) : d114204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115279, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d112688 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12352 q = 1) (hb : d112688 q = 1) : d114207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32652 q ha hb
    | true =>
      simp only [d12352, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12353 q = 1) (hb : d112688 q = 1) : d114208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12354 q = 1) (hb : d112688 q = 1) : d114209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12354, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12355 q = 1) (hb : d112688 q = 1) : d114210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d112688 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12357 q = 1) (hb : d112688 q = 1) : d114212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32653 q ha hb
    | true =>
      simp only [d12357, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12358 q = 1) (hb : d112688 q = 1) : d114213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12359 q = 1) (hb : d112688 q = 1) : d114214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12359, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12361 q = 1) (hb : d112688 q = 1) : d114216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32654 q ha hb
    | true =>
      simp only [d12361, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32636 q ha hb
  have h27 (q : Pattern) (ha : d112688 q = 1) (hb : d115281 q = 1) : d114217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d115281, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d12366 q = 1) (hb : d112688 q = 1) : d114219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32655 q ha hb
    | true =>
      simp only [d12366, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12367 q = 1) (hb : d112688 q = 1) : d114220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12367, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d112688 q = 1) (hb : d115282 q = 1) : d114221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115282, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d112688 q = 1) (hb : d115283 q = 1) : d114222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d115283, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d112688 q = 1) (hb : d115284 q = 1) : d114223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115284, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d112688 q = 1) (hb : d115285 q = 1) : d114224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115285, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro32657 (p : Pattern) (ha : d112688 p = 1) (hb : d115292 p = 1) : d114233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d112688 q = 1) : d114216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32654 q ha hb
    | true =>
      simp only [d12361, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32636 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115281 q = 1) : d114217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115281, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d112688 q = 1) : d114219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32655 q ha hb
    | true =>
      simp only [d12366, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d112688 q = 1) : d114220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115282 q = 1) : d114221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115290 q = 1) : d114231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115290, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115291 q = 1) : d114232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115291, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115292 q = 1) : d114233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115292, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32658 (p : Pattern) (ha : d12392 p = 1) (hb : d112688 p = 1) : d114241 p = 1 := by
  have h0 (q : Pattern) (ha : d12389 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6078 q = 1) (hb : d94753 q = 1) : d6078 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6079, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12390 q = 1) (hb : d112687 q = 1) : d114239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d112687, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12390, d112687, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12259 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12391 q = 1) (hb : d112688 q = 1) : d114240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d112688, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12391, d112688, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12392 q = 1) (hb : d112688 q = 1) : d114241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12392, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32659 (p : Pattern) (ha : d12398 p = 1) (hb : d112688 p = 1) : d114247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32658 q ha hb
    | true =>
      simp only [d12393, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d112688 q = 1) : d114135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32639 q ha hb
    | true =>
      simp only [d12262, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d112688 q = 1) : d114136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d112688 q = 1) : d114244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d112688 q = 1) : d114245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d112688 q = 1) : d114246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d112688 q = 1) : d114247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32660 (p : Pattern) (ha : d12418 p = 1) (hb : d112688 p = 1) : d114253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d112688 q = 1) : d114135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32639 q ha hb
    | true =>
      simp only [d12262, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d112688 q = 1) : d114136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d112688 q = 1) : d114250 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d112688 q = 1) : d114251 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d112688 q = 1) : d114252 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d112688 q = 1) : d114253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32661 (p : Pattern) (ha : d112688 p = 1) (hb : d115302 p = 1) : d114259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d112688 q = 1) : d114248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32659 q ha hb
    | true =>
      simp only [d12399, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32640 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115298 q = 1) : d114249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115298, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d112688 q = 1) : d114254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32660 q ha hb
    | true =>
      simp only [d12419, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d112688 q = 1) : d114255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115299 q = 1) : d114256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115300 q = 1) : d114257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115300, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115301 q = 1) : d114258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115301, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115302 q = 1) : d114259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115302, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32662 (p : Pattern) (ha : d112688 p = 1) (hb : d115308 p = 1) : d114265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d112688 q = 1) : d114163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32643 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d112688 q = 1) : d114164 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d112688 q = 1) : d114170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32643 q ha hb
    | true =>
      simp only [d12297, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32644 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d112688 q = 1) : d114171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d112688 q = 1) : d114172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115286 q = 1) : d114225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32651 q ha hb
    | true =>
      simp only [d115286, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32656 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d112688 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12374 q = 1) (hb : d112688 q = 1) : d114227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32645 q ha hb
    | true =>
      simp only [d12374, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115287 q = 1) : d114228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115288 q = 1) : d114229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115288, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115289 q = 1) : d114230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115289, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115293 q = 1) : d114234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115293, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32657 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d112688 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115294 q = 1) : d114235 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115294, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115295 q = 1) : d114236 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115295, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115296 q = 1) : d114237 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115296, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115297 q = 1) : d114238 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115297, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115303 q = 1) : d114260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115303, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32661 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d112688 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d112688 q = 1) (hb : d115304 q = 1) : d114261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115304, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d112688 q = 1) (hb : d115305 q = 1) : d114262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115305, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112688 q = 1) (hb : d115306 q = 1) : d114263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115306, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112688 q = 1) (hb : d115307 q = 1) : d114264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115307, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d112688 q = 1) (hb : d115308 q = 1) : d114265 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115308, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro32663 (p : Pattern) (ha : d112688 p = 1) (hb : d115314 p = 1) : d114271 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d112688 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115271 q = 1) : d114153 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115271, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32642 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115272 q = 1) : d114154 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115272, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115273 q = 1) : d114155 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115273, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115274 q = 1) : d114156 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115274, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115275 q = 1) : d114157 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115275, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115309 q = 1) : d114266 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115309, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32662 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115310 q = 1) : d114267 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115310, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115311 q = 1) : d114268 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115311, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115312 q = 1) : d114269 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115312, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115313 q = 1) : d114270 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115313, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115314 q = 1) : d114271 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115314, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro32664 (p : Pattern) (ha : d12438 p = 1) (hb : d112688 p = 1) : d114187 p = 1 := by
  have h0 (q : Pattern) (ha : d12315 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4818 q = 1) (hb : d94753 q = 1) : d4818 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4819, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12316 q = 1) (hb : d112687 q = 1) : d114185 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d112687, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12316, d112687, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d4822 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12437 q = 1) (hb : d112688 q = 1) : d114186 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d112688, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12437, d112688, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12438 q = 1) (hb : d112688 q = 1) : d114187 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12438, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32665 (p : Pattern) (ha : d12448 p = 1) (hb : d112688 p = 1) : d114275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12447 q = 1) (hb : d112688 q = 1) : d114274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12447, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12448 q = 1) (hb : d112688 q = 1) : d114275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32666 (p : Pattern) (ha : d12458 p = 1) (hb : d112688 p = 1) : d114281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d112688 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d112688 q = 1) : d114276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32665 q ha hb
    | true =>
      simp only [d12453, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d112688 q = 1) : d114277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d112688 q = 1) : d114278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d112688 q = 1) : d114279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d112688 q = 1) : d114280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12458 q = 1) (hb : d112688 q = 1) : d114281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32667 (p : Pattern) (ha : d12461 p = 1) (hb : d112688 p = 1) : d114284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12447 q = 1) (hb : d112688 q = 1) : d114274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12447, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12461 q = 1) (hb : d112688 q = 1) : d114284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12461, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32668 (p : Pattern) (ha : d12468 p = 1) (hb : d112688 p = 1) : d114290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d112688 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d112688 q = 1) : d114276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32665 q ha hb
    | true =>
      simp only [d12453, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d112688 q = 1) : d114277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d112688 q = 1) : d114278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d112688 q = 1) : d114279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d112688 q = 1) : d114280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12462 q = 1) (hb : d112688 q = 1) : d12462 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12463 q = 1) (hb : d112688 q = 1) : d114285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32667 q ha hb
    | true =>
      simp only [d12463, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12464 q = 1) (hb : d112688 q = 1) : d114286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12465 q = 1) (hb : d112688 q = 1) : d114287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12465, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12466 q = 1) (hb : d112688 q = 1) : d114288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12467 q = 1) (hb : d112688 q = 1) : d114289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12468 q = 1) (hb : d112688 q = 1) : d114290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12468, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro32669 (p : Pattern) (ha : d12574 p = 1) (hb : d112688 p = 1) : d114350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d112688 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d112688 q = 1) : d114276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32665 q ha hb
    | true =>
      simp only [d12453, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d112688 q = 1) : d114277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d112688 q = 1) : d114278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d112688 q = 1) : d114279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d112688 q = 1) : d114280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12573 q = 1) (hb : d112688 q = 1) : d12573 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12574 q = 1) (hb : d112688 q = 1) : d114350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12574, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32670 (p : Pattern) (ha : d12473 p = 1) (hb : d112688 p = 1) : d114295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12472 q = 1) (hb : d112688 q = 1) : d114294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12473 q = 1) (hb : d112688 q = 1) : d114295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32671 (p : Pattern) (ha : d12482 p = 1) (hb : d112688 p = 1) : d114302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12480 q = 1) (hb : d112688 q = 1) : d114300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12481 q = 1) (hb : d112688 q = 1) : d114301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12481, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12482 q = 1) (hb : d112688 q = 1) : d114302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32672 (p : Pattern) (ha : d12502 p = 1) (hb : d112688 p = 1) : d114311 p = 1 := by
  have h0 (q : Pattern) (ha : d12492 q = 1) (hb : d94753 q = 1) : d12492 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12312 q = 1) (hb : d94753 q = 1) : d12312 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12496 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12497 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12497, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d12498 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12498, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12499 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12499, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12500 q = 1) (hb : d112687 q = 1) : d114309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d112687, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12500, d112687, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12316 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12501 q = 1) (hb : d112688 q = 1) : d114310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d112688, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12501, d112688, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12502 q = 1) (hb : d112688 q = 1) : d114311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12502, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32673 (p : Pattern) (ha : d12508 p = 1) (hb : d112688 p = 1) : d114317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d112688 q = 1) : d114312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32672 q ha hb
    | true =>
      simp only [d12503, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d112688 q = 1) : d114313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d112688 q = 1) : d114314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d112688 q = 1) : d114315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d112688 q = 1) : d114316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d112688 q = 1) : d114317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32674 (p : Pattern) (ha : d12537 p = 1) (hb : d112688 p = 1) : d114323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d112688 q = 1) : d114320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d112688 q = 1) : d114321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d112688 q = 1) : d114322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d112688 q = 1) : d114323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32675 (p : Pattern) (ha : d112688 p = 1) (hb : d115319 p = 1) : d114329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12475 q = 1) (hb : d112688 q = 1) : d12475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12476 q = 1) (hb : d112688 q = 1) : d114296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32670 q ha hb
    | true =>
      simp only [d12476, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12477 q = 1) (hb : d112688 q = 1) : d114297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12478 q = 1) (hb : d112688 q = 1) : d114298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12478, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12479 q = 1) (hb : d112688 q = 1) : d114299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d112688 q = 1) : d12485 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12486 q = 1) (hb : d112688 q = 1) : d114303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32671 q ha hb
    | true =>
      simp only [d12486, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12487 q = 1) (hb : d112688 q = 1) : d114304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12488 q = 1) (hb : d112688 q = 1) : d114305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12488, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12509 q = 1) (hb : d112688 q = 1) : d114318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32673 q ha hb
    | true =>
      simp only [d12509, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32665 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115315 q = 1) : d114319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115315, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12538 q = 1) (hb : d112688 q = 1) : d114324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32674 q ha hb
    | true =>
      simp only [d12538, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12539 q = 1) (hb : d112688 q = 1) : d114325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12539, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115316 q = 1) : d114326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115316, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115317 q = 1) : d114327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115317, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115318 q = 1) : d114328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115318, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115319 q = 1) : d114329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115319, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32676 (p : Pattern) (ha : d12544 p = 1) (hb : d112688 p = 1) : d114330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12472 q = 1) (hb : d112688 q = 1) : d114294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12544 q = 1) (hb : d112688 q = 1) : d114330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12544, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32677 (p : Pattern) (ha : d12550 p = 1) (hb : d112688 p = 1) : d114335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12480 q = 1) (hb : d112688 q = 1) : d114300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12481 q = 1) (hb : d112688 q = 1) : d114301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12481, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12550 q = 1) (hb : d112688 q = 1) : d114335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12550, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32678 (p : Pattern) (ha : d12555 p = 1) (hb : d112688 p = 1) : d114339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d112688 q = 1) : d114312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32672 q ha hb
    | true =>
      simp only [d12503, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d112688 q = 1) : d114313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d112688 q = 1) : d114314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d112688 q = 1) : d114315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d112688 q = 1) : d114316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d112688 q = 1) : d114339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32679 (p : Pattern) (ha : d12561 p = 1) (hb : d112688 p = 1) : d114342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32664 q ha hb
    | true =>
      simp only [d12439, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d112688 q = 1) : d114320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d112688 q = 1) : d114321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d112688 q = 1) : d114322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d112688 q = 1) : d114342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32680 (p : Pattern) (ha : d112688 p = 1) (hb : d115324 p = 1) : d114348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12475 q = 1) (hb : d112688 q = 1) : d12475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12476 q = 1) (hb : d112688 q = 1) : d114296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32670 q ha hb
    | true =>
      simp only [d12476, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12477 q = 1) (hb : d112688 q = 1) : d114297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12478 q = 1) (hb : d112688 q = 1) : d114298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12478, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12479 q = 1) (hb : d112688 q = 1) : d114299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d112688 q = 1) : d12485 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12486 q = 1) (hb : d112688 q = 1) : d114303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32671 q ha hb
    | true =>
      simp only [d12486, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12487 q = 1) (hb : d112688 q = 1) : d114304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12488 q = 1) (hb : d112688 q = 1) : d114305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12488, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12509 q = 1) (hb : d112688 q = 1) : d114318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32673 q ha hb
    | true =>
      simp only [d12509, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32665 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115315 q = 1) : d114319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115315, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12538 q = 1) (hb : d112688 q = 1) : d114324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32674 q ha hb
    | true =>
      simp only [d12538, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12539 q = 1) (hb : d112688 q = 1) : d114325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12539, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115316 q = 1) : d114326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115316, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115317 q = 1) : d114327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115317, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115318 q = 1) : d114328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115318, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12545 q = 1) (hb : d112688 q = 1) : d12545 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12546 q = 1) (hb : d112688 q = 1) : d114331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32676 q ha hb
    | true =>
      simp only [d12546, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12547 q = 1) (hb : d112688 q = 1) : d114332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12548 q = 1) (hb : d112688 q = 1) : d114333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12548, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12549 q = 1) (hb : d112688 q = 1) : d114334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12551 q = 1) (hb : d112688 q = 1) : d12551 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12552 q = 1) (hb : d112688 q = 1) : d114336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32677 q ha hb
    | true =>
      simp only [d12552, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12553 q = 1) (hb : d112688 q = 1) : d114337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12554 q = 1) (hb : d112688 q = 1) : d114338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12554, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12556 q = 1) (hb : d112688 q = 1) : d114340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32678 q ha hb
    | true =>
      simp only [d12556, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32667 q ha hb
  have h27 (q : Pattern) (ha : d112688 q = 1) (hb : d115320 q = 1) : d114341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d115320, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d12562 q = 1) (hb : d112688 q = 1) : d114343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32679 q ha hb
    | true =>
      simp only [d12562, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12563 q = 1) (hb : d112688 q = 1) : d114344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12563, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d112688 q = 1) (hb : d115321 q = 1) : d114345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115321, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d112688 q = 1) (hb : d115322 q = 1) : d114346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d115322, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d112688 q = 1) (hb : d115323 q = 1) : d114347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115323, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d112688 q = 1) (hb : d115324 q = 1) : d114348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115324, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro32681 (p : Pattern) (ha : d112688 p = 1) (hb : d115331 p = 1) : d114357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d112688 q = 1) : d114340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32678 q ha hb
    | true =>
      simp only [d12556, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32667 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115320 q = 1) : d114341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115320, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d112688 q = 1) : d114343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32679 q ha hb
    | true =>
      simp only [d12562, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d112688 q = 1) : d114344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115321 q = 1) : d114345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115329 q = 1) : d114355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115329, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115330 q = 1) : d114356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115330, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115331 q = 1) : d114357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115331, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32682 (p : Pattern) (ha : d12610 p = 1) (hb : d112688 p = 1) : d114368 p = 1 := by
  have h0 (q : Pattern) (ha : d12598 q = 1) (hb : d94753 q = 1) : d12598 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12386 q = 1) (hb : d94753 q = 1) : d12386 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12604 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12605 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12605, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d12606 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12606, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12607 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12607, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12608 q = 1) (hb : d112687 q = 1) : d114366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d112687, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12608, d112687, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12390 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12609 q = 1) (hb : d112688 q = 1) : d114367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d112688, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12609, d112688, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12610 q = 1) (hb : d112688 q = 1) : d114368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12610, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32683 (p : Pattern) (ha : d12614 p = 1) (hb : d112688 p = 1) : d114241 p = 1 := by
  have h0 (q : Pattern) (ha : d12389 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6078 q = 1) (hb : d94753 q = 1) : d6078 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6079, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12390 q = 1) (hb : d112687 q = 1) : d114239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d112687, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12390, d112687, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d6082 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12613 q = 1) (hb : d112688 q = 1) : d114240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d112688, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12613, d112688, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12614 q = 1) (hb : d112688 q = 1) : d114241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12614, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32684 (p : Pattern) (ha : d12620 p = 1) (hb : d112688 p = 1) : d114374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d112688 q = 1) : d114369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32682 q ha hb
    | true =>
      simp only [d12611, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d112688 q = 1) : d114370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32683 q ha hb
    | true =>
      simp only [d12615, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d112688 q = 1) : d114371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d112688 q = 1) : d114372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d112688 q = 1) : d114373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d112688 q = 1) : d114374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32685 (p : Pattern) (ha : d12628 p = 1) (hb : d112688 p = 1) : d114378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32683 q ha hb
    | true =>
      simp only [d12615, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12624 q = 1) (hb : d112688 q = 1) : d12624 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12625 q = 1) (hb : d112688 q = 1) : d114375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12626 q = 1) (hb : d112688 q = 1) : d114376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12626, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12627 q = 1) (hb : d112688 q = 1) : d114377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12627, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12628 q = 1) (hb : d112688 q = 1) : d114378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12628, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32686 (p : Pattern) (ha : d12657 p = 1) (hb : d112688 p = 1) : d114384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32683 q ha hb
    | true =>
      simp only [d12615, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d112688 q = 1) : d114381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d112688 q = 1) : d114382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d112688 q = 1) : d114383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d112688 q = 1) : d114384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32687 (p : Pattern) (ha : d112688 p = 1) (hb : d115341 p = 1) : d114390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d112688 q = 1) : d114379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32684 q ha hb
    | true =>
      simp only [d12629, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32685 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115337 q = 1) : d114380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115337, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d112688 q = 1) : d114385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32686 q ha hb
    | true =>
      simp only [d12658, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d112688 q = 1) : d114386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115338 q = 1) : d114387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115339 q = 1) : d114388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115339, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115340 q = 1) : d114389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115340, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115341 q = 1) : d114390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115341, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32688 (p : Pattern) (ha : d112688 p = 1) (hb : d115347 p = 1) : d114396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d112688 q = 1) : d114282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32666 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d112688 q = 1) : d114283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d112688 q = 1) : d114291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32666 q ha hb
    | true =>
      simp only [d12469, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32668 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d112688 q = 1) : d114292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d112688 q = 1) : d114293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115325 q = 1) : d114349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32675 q ha hb
    | true =>
      simp only [d115325, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32680 q ha hb
  have h7 (q : Pattern) (ha : d12580 q = 1) (hb : d112688 q = 1) : d12580 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12581 q = 1) (hb : d112688 q = 1) : d114351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32669 q ha hb
    | true =>
      simp only [d12581, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115326 q = 1) : d114352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115327 q = 1) : d114353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115327, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115328 q = 1) : d114354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115328, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115332 q = 1) : d114358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115332, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32681 q ha hb
  have h13 (q : Pattern) (ha : d12590 q = 1) (hb : d112688 q = 1) : d12590 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115333 q = 1) : d114359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115333, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115334 q = 1) : d114360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115334, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115335 q = 1) : d114361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115335, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115336 q = 1) : d114362 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115336, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115342 q = 1) : d114391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115342, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32687 q ha hb
  have h19 (q : Pattern) (ha : d12675 q = 1) (hb : d112688 q = 1) : d12675 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d112688 q = 1) (hb : d115343 q = 1) : d114392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115343, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d112688 q = 1) (hb : d115344 q = 1) : d114393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115344, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112688 q = 1) (hb : d115345 q = 1) : d114394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115345, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112688 q = 1) (hb : d115346 q = 1) : d114395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115346, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d112688 q = 1) (hb : d115347 q = 1) : d114396 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115347, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro32689 (p : Pattern) (ha : d112688 p = 1) (hb : d115353 p = 1) : d114402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115348 q = 1) : d114397 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115348, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32688 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115349 q = 1) : d114398 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115349, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115350 q = 1) : d114399 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115350, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115351 q = 1) : d114400 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115351, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115352 q = 1) : d114401 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115352, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115353 q = 1) : d114402 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115353, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32690 (p : Pattern) (ha : d12693 p = 1) (hb : d112688 p = 1) : d114406 p = 1 := by
  have h0 (q : Pattern) (ha : d12690 q = 1) (hb : d94753 q = 1) : d12690 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4913 q = 1) (hb : d94753 q = 1) : d4913 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4914 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4914, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d4915 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4915, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4916 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4916, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12691 q = 1) (hb : d112687 q = 1) : d114404 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d112687, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12691, d112687, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d4917 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12692 q = 1) (hb : d112688 q = 1) : d114405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d112688, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12692, d112688, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12693 q = 1) (hb : d112688 q = 1) : d114406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12693, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32691 (p : Pattern) (ha : d12703 p = 1) (hb : d112688 p = 1) : d114412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12702 q = 1) (hb : d112688 q = 1) : d114411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12702, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12703 q = 1) (hb : d112688 q = 1) : d114412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32692 (p : Pattern) (ha : d12713 p = 1) (hb : d112688 p = 1) : d114418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d112688 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d112688 q = 1) : d114413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32691 q ha hb
    | true =>
      simp only [d12708, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d112688 q = 1) : d114414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d112688 q = 1) : d114415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d112688 q = 1) : d114416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d112688 q = 1) : d114417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12713 q = 1) (hb : d112688 q = 1) : d114418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32693 (p : Pattern) (ha : d12716 p = 1) (hb : d112688 p = 1) : d114421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12702 q = 1) (hb : d112688 q = 1) : d114411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12702, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12716 q = 1) (hb : d112688 q = 1) : d114421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12716, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32694 (p : Pattern) (ha : d12723 p = 1) (hb : d112688 p = 1) : d114427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d112688 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d112688 q = 1) : d114413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32691 q ha hb
    | true =>
      simp only [d12708, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d112688 q = 1) : d114414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d112688 q = 1) : d114415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d112688 q = 1) : d114416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d112688 q = 1) : d114417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12717 q = 1) (hb : d112688 q = 1) : d12717 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12718 q = 1) (hb : d112688 q = 1) : d114422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32693 q ha hb
    | true =>
      simp only [d12718, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12719 q = 1) (hb : d112688 q = 1) : d114423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12720 q = 1) (hb : d112688 q = 1) : d114424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12720, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12721 q = 1) (hb : d112688 q = 1) : d114425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12722 q = 1) (hb : d112688 q = 1) : d114426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12723 q = 1) (hb : d112688 q = 1) : d114427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12723, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro32695 (p : Pattern) (ha : d12833 p = 1) (hb : d112688 p = 1) : d114487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d112688 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d112688 q = 1) : d114413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32691 q ha hb
    | true =>
      simp only [d12708, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d112688 q = 1) : d114414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d112688 q = 1) : d114415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d112688 q = 1) : d114416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d112688 q = 1) : d114417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12832 q = 1) (hb : d112688 q = 1) : d12832 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12833 q = 1) (hb : d112688 q = 1) : d114487 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12833, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32696 (p : Pattern) (ha : d12728 p = 1) (hb : d112688 p = 1) : d114432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12727 q = 1) (hb : d112688 q = 1) : d114431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12728 q = 1) (hb : d112688 q = 1) : d114432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32697 (p : Pattern) (ha : d12737 p = 1) (hb : d112688 p = 1) : d114439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12735 q = 1) (hb : d112688 q = 1) : d114437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12736 q = 1) (hb : d112688 q = 1) : d114438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12736, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12737 q = 1) (hb : d112688 q = 1) : d114439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32698 (p : Pattern) (ha : d12757 p = 1) (hb : d112688 p = 1) : d114448 p = 1 := by
  have h0 (q : Pattern) (ha : d12747 q = 1) (hb : d94753 q = 1) : d12747 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12489 q = 1) (hb : d94753 q = 1) : d12489 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12751 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12752 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12752, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d12753 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12753, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12754 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12754, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12755 q = 1) (hb : d112687 q = 1) : d114446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d112687, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12755, d112687, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12691 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12756 q = 1) (hb : d112688 q = 1) : d114447 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d112688, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12756, d112688, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12757 q = 1) (hb : d112688 q = 1) : d114448 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12757, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32699 (p : Pattern) (ha : d12763 p = 1) (hb : d112688 p = 1) : d114454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d112688 q = 1) : d114449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32698 q ha hb
    | true =>
      simp only [d12758, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d112688 q = 1) : d114450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d112688 q = 1) : d114451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d112688 q = 1) : d114452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d112688 q = 1) : d114453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d112688 q = 1) : d114454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32700 (p : Pattern) (ha : d12796 p = 1) (hb : d112688 p = 1) : d114460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d112688 q = 1) : d114457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d112688 q = 1) : d114458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d112688 q = 1) : d114459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d112688 q = 1) : d114460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32701 (p : Pattern) (ha : d112688 p = 1) (hb : d115359 p = 1) : d114466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12730 q = 1) (hb : d112688 q = 1) : d12730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12731 q = 1) (hb : d112688 q = 1) : d114433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32696 q ha hb
    | true =>
      simp only [d12731, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12732 q = 1) (hb : d112688 q = 1) : d114434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12733 q = 1) (hb : d112688 q = 1) : d114435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12733, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12734 q = 1) (hb : d112688 q = 1) : d114436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d112688 q = 1) : d12740 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12741 q = 1) (hb : d112688 q = 1) : d114440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32697 q ha hb
    | true =>
      simp only [d12741, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12742 q = 1) (hb : d112688 q = 1) : d114441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12743 q = 1) (hb : d112688 q = 1) : d114442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12743, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12764 q = 1) (hb : d112688 q = 1) : d114455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32699 q ha hb
    | true =>
      simp only [d12764, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32691 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115355 q = 1) : d114456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115355, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12797 q = 1) (hb : d112688 q = 1) : d114461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32700 q ha hb
    | true =>
      simp only [d12797, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12798 q = 1) (hb : d112688 q = 1) : d114462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12798, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115356 q = 1) : d114463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115356, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115357 q = 1) : d114464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115357, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115358 q = 1) : d114465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115358, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115359 q = 1) : d114466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115359, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32702 (p : Pattern) (ha : d12803 p = 1) (hb : d112688 p = 1) : d114467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12727 q = 1) (hb : d112688 q = 1) : d114431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12803 q = 1) (hb : d112688 q = 1) : d114467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12803, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32703 (p : Pattern) (ha : d12809 p = 1) (hb : d112688 p = 1) : d114472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12735 q = 1) (hb : d112688 q = 1) : d114437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12736 q = 1) (hb : d112688 q = 1) : d114438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12736, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12809 q = 1) (hb : d112688 q = 1) : d114472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12809, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32704 (p : Pattern) (ha : d12814 p = 1) (hb : d112688 p = 1) : d114476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d112688 q = 1) : d114449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32698 q ha hb
    | true =>
      simp only [d12758, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d112688 q = 1) : d114450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d112688 q = 1) : d114451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d112688 q = 1) : d114452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d112688 q = 1) : d114453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d112688 q = 1) : d114476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32705 (p : Pattern) (ha : d12820 p = 1) (hb : d112688 p = 1) : d114479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32690 q ha hb
    | true =>
      simp only [d12694, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d112688 q = 1) : d114457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d112688 q = 1) : d114458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d112688 q = 1) : d114459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d112688 q = 1) : d114479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32706 (p : Pattern) (ha : d112688 p = 1) (hb : d115364 p = 1) : d114485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12730 q = 1) (hb : d112688 q = 1) : d12730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12731 q = 1) (hb : d112688 q = 1) : d114433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32696 q ha hb
    | true =>
      simp only [d12731, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12732 q = 1) (hb : d112688 q = 1) : d114434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12733 q = 1) (hb : d112688 q = 1) : d114435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12733, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12734 q = 1) (hb : d112688 q = 1) : d114436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d112688 q = 1) : d12740 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12741 q = 1) (hb : d112688 q = 1) : d114440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32697 q ha hb
    | true =>
      simp only [d12741, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12742 q = 1) (hb : d112688 q = 1) : d114441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12743 q = 1) (hb : d112688 q = 1) : d114442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12743, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12764 q = 1) (hb : d112688 q = 1) : d114455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32699 q ha hb
    | true =>
      simp only [d12764, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32691 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115355 q = 1) : d114456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115355, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12797 q = 1) (hb : d112688 q = 1) : d114461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32700 q ha hb
    | true =>
      simp only [d12797, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12798 q = 1) (hb : d112688 q = 1) : d114462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12798, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115356 q = 1) : d114463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115356, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115357 q = 1) : d114464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115357, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115358 q = 1) : d114465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115358, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12804 q = 1) (hb : d112688 q = 1) : d12804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12805 q = 1) (hb : d112688 q = 1) : d114468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32702 q ha hb
    | true =>
      simp only [d12805, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12806 q = 1) (hb : d112688 q = 1) : d114469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12807 q = 1) (hb : d112688 q = 1) : d114470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12807, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12808 q = 1) (hb : d112688 q = 1) : d114471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12810 q = 1) (hb : d112688 q = 1) : d12810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12811 q = 1) (hb : d112688 q = 1) : d114473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32703 q ha hb
    | true =>
      simp only [d12811, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12812 q = 1) (hb : d112688 q = 1) : d114474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12813 q = 1) (hb : d112688 q = 1) : d114475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12813, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12815 q = 1) (hb : d112688 q = 1) : d114477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32704 q ha hb
    | true =>
      simp only [d12815, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32693 q ha hb
  have h27 (q : Pattern) (ha : d112688 q = 1) (hb : d115360 q = 1) : d114478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d115360, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d12821 q = 1) (hb : d112688 q = 1) : d114480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32705 q ha hb
    | true =>
      simp only [d12821, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12822 q = 1) (hb : d112688 q = 1) : d114481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12822, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d112688 q = 1) (hb : d115361 q = 1) : d114482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115361, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d112688 q = 1) (hb : d115362 q = 1) : d114483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d115362, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d112688 q = 1) (hb : d115363 q = 1) : d114484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115363, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d112688 q = 1) (hb : d115364 q = 1) : d114485 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115364, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro32707 (p : Pattern) (ha : d112688 p = 1) (hb : d115371 p = 1) : d114494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d112688 q = 1) : d114477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32704 q ha hb
    | true =>
      simp only [d12815, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32693 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115360 q = 1) : d114478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115360, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d112688 q = 1) : d114480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32705 q ha hb
    | true =>
      simp only [d12821, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d112688 q = 1) : d114481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115361 q = 1) : d114482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115369 q = 1) : d114492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115369, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115370 q = 1) : d114493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115370, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115371 q = 1) : d114494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115371, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32708 (p : Pattern) (ha : d12873 p = 1) (hb : d112688 p = 1) : d114505 p = 1 := by
  have h0 (q : Pattern) (ha : d12857 q = 1) (hb : d94753 q = 1) : d12857 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12595 q = 1) (hb : d94753 q = 1) : d12595 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12863 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12864 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12864, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d12865 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12865, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12866 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12866, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12867 q = 1) (hb : d112687 q = 1) : d114503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d112687, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12867, d112687, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12871 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12872 q = 1) (hb : d112688 q = 1) : d114504 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d112688, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12872, d112688, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12873 q = 1) (hb : d112688 q = 1) : d114505 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12873, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32709 (p : Pattern) (ha : d12877 p = 1) (hb : d112688 p = 1) : d114510 p = 1 := by
  have h0 (q : Pattern) (ha : d12870 q = 1) (hb : d94753 q = 1) : d12870 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6210 q = 1) (hb : d94753 q = 1) : d6210 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6211 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6211, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6212 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6212, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6213 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6213, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12871 q = 1) (hb : d112687 q = 1) : d114508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d112687, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12871, d112687, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d6214 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12876 q = 1) (hb : d112688 q = 1) : d114509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d112688, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12876, d112688, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12877 q = 1) (hb : d112688 q = 1) : d114510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12877, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32710 (p : Pattern) (ha : d12883 p = 1) (hb : d112688 p = 1) : d114516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d112688 q = 1) : d114506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32708 q ha hb
    | true =>
      simp only [d12874, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d112688 q = 1) : d114507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d112688 q = 1) : d114511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32709 q ha hb
    | true =>
      simp only [d12878, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d112688 q = 1) : d114512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d112688 q = 1) : d114513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d112688 q = 1) : d114514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d112688 q = 1) : d114515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d112688 q = 1) : d114516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32711 (p : Pattern) (ha : d12891 p = 1) (hb : d112688 p = 1) : d114520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d112688 q = 1) : d114511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32709 q ha hb
    | true =>
      simp only [d12878, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d112688 q = 1) : d114512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12887 q = 1) (hb : d112688 q = 1) : d12887 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12888 q = 1) (hb : d112688 q = 1) : d114517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12889 q = 1) (hb : d112688 q = 1) : d114518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12889, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12890 q = 1) (hb : d112688 q = 1) : d114519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12890, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12891 q = 1) (hb : d112688 q = 1) : d114520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12891, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32712 (p : Pattern) (ha : d12924 p = 1) (hb : d112688 p = 1) : d114526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d112688 q = 1) : d114511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32709 q ha hb
    | true =>
      simp only [d12878, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d112688 q = 1) : d114512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d112688 q = 1) : d114523 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d112688 q = 1) : d114524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d112688 q = 1) : d114525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d112688 q = 1) : d114526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32713 (p : Pattern) (ha : d112688 p = 1) (hb : d115381 p = 1) : d114532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d112688 q = 1) : d114521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32710 q ha hb
    | true =>
      simp only [d12892, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32711 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115377 q = 1) : d114522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115377, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d112688 q = 1) : d114527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32712 q ha hb
    | true =>
      simp only [d12925, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d112688 q = 1) : d114528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115378 q = 1) : d114529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115379 q = 1) : d114530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115379, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115380 q = 1) : d114531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115380, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115381 q = 1) : d114532 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115381, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32714 (p : Pattern) (ha : d112688 p = 1) (hb : d115387 p = 1) : d114538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d112688 q = 1) : d114419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32692 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d112688 q = 1) : d114420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d112688 q = 1) : d114428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32692 q ha hb
    | true =>
      simp only [d12724, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32694 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d112688 q = 1) : d114429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d112688 q = 1) : d114430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115365 q = 1) : d114486 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32701 q ha hb
    | true =>
      simp only [d115365, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32706 q ha hb
  have h7 (q : Pattern) (ha : d12839 q = 1) (hb : d112688 q = 1) : d12839 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12840 q = 1) (hb : d112688 q = 1) : d114488 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32695 q ha hb
    | true =>
      simp only [d12840, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115366 q = 1) : d114489 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115367 q = 1) : d114490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115367, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115368 q = 1) : d114491 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115368, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115372 q = 1) : d114495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115372, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32707 q ha hb
  have h13 (q : Pattern) (ha : d12849 q = 1) (hb : d112688 q = 1) : d12849 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115373 q = 1) : d114496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115373, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115374 q = 1) : d114497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115374, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115375 q = 1) : d114498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115375, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115376 q = 1) : d114499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115376, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115382 q = 1) : d114533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115382, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32713 q ha hb
  have h19 (q : Pattern) (ha : d12942 q = 1) (hb : d112688 q = 1) : d12942 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d112688 q = 1) (hb : d115383 q = 1) : d114534 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115383, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d112688 q = 1) (hb : d115384 q = 1) : d114535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115384, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112688 q = 1) (hb : d115385 q = 1) : d114536 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115385, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112688 q = 1) (hb : d115386 q = 1) : d114537 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115386, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d112688 q = 1) (hb : d115387 q = 1) : d114538 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115387, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro32715 (p : Pattern) (ha : d112688 p = 1) (hb : d115393 p = 1) : d114544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115388 q = 1) : d114539 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115388, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32714 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115389 q = 1) : d114540 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115389, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115390 q = 1) : d114541 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115390, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115391 q = 1) : d114542 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115391, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115392 q = 1) : d114543 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115392, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115393 q = 1) : d114544 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115393, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32716 (p : Pattern) (ha : d12967 p = 1) (hb : d112688 p = 1) : d114549 p = 1 := by
  have h0 (q : Pattern) (ha : d12959 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5009 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5024, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d112687 q = 1) : d114547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d112687, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12960, d112687, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12965 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12966 q = 1) (hb : d112688 q = 1) : d114548 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d112688, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12966, d112688, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12967 q = 1) (hb : d112688 q = 1) : d114549 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12967, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32717 (p : Pattern) (ha : d12977 p = 1) (hb : d112688 p = 1) : d114555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12976 q = 1) (hb : d112688 q = 1) : d114554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12976, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12977 q = 1) (hb : d112688 q = 1) : d114555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32718 (p : Pattern) (ha : d12987 p = 1) (hb : d112688 p = 1) : d114561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12981 q = 1) (hb : d112688 q = 1) : d12981 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12982 q = 1) (hb : d112688 q = 1) : d114556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32717 q ha hb
    | true =>
      simp only [d12982, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12983 q = 1) (hb : d112688 q = 1) : d114557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12984 q = 1) (hb : d112688 q = 1) : d114558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12984, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12985 q = 1) (hb : d112688 q = 1) : d114559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12986 q = 1) (hb : d112688 q = 1) : d114560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12987 q = 1) (hb : d112688 q = 1) : d114561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32719 (p : Pattern) (ha : d12990 p = 1) (hb : d112688 p = 1) : d114564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12976 q = 1) (hb : d112688 q = 1) : d114554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12976, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12990 q = 1) (hb : d112688 q = 1) : d114564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12990, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32720 (p : Pattern) (ha : d12997 p = 1) (hb : d112688 p = 1) : d114570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12981 q = 1) (hb : d112688 q = 1) : d12981 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12982 q = 1) (hb : d112688 q = 1) : d114556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32717 q ha hb
    | true =>
      simp only [d12982, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12983 q = 1) (hb : d112688 q = 1) : d114557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12984 q = 1) (hb : d112688 q = 1) : d114558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12984, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12985 q = 1) (hb : d112688 q = 1) : d114559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12986 q = 1) (hb : d112688 q = 1) : d114560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12991 q = 1) (hb : d112688 q = 1) : d12991 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12992 q = 1) (hb : d112688 q = 1) : d114565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32719 q ha hb
    | true =>
      simp only [d12992, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12993 q = 1) (hb : d112688 q = 1) : d114566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12994 q = 1) (hb : d112688 q = 1) : d114567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12994, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12995 q = 1) (hb : d112688 q = 1) : d114568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12996 q = 1) (hb : d112688 q = 1) : d114569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12997 q = 1) (hb : d112688 q = 1) : d114570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12997, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro32721 (p : Pattern) (ha : d13040 p = 1) (hb : d112688 p = 1) : d114549 p = 1 := by
  have h0 (q : Pattern) (ha : d12959 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5009 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5024, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d112687 q = 1) : d114547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d112687, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12960, d112687, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d5027 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13039 q = 1) (hb : d112688 q = 1) : d114548 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d112688, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13039, d112688, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13040 q = 1) (hb : d112688 q = 1) : d114549 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13040, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32722 (p : Pattern) (ha : d13050 p = 1) (hb : d112688 p = 1) : d114555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32721 q ha hb
    | true =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13047 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13048 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13048, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13049 q = 1) (hb : d112688 q = 1) : d114554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13049, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13050 q = 1) (hb : d112688 q = 1) : d114555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32723 (p : Pattern) (ha : d13134 p = 1) (hb : d112688 p = 1) : d114630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12981 q = 1) (hb : d112688 q = 1) : d12981 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13124 q = 1) (hb : d112688 q = 1) : d114556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32722 q ha hb
    | true =>
      simp only [d13124, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13125 q = 1) (hb : d112688 q = 1) : d114557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13126 q = 1) (hb : d112688 q = 1) : d114558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13126, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13127 q = 1) (hb : d112688 q = 1) : d114559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13128 q = 1) (hb : d112688 q = 1) : d114560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13133 q = 1) (hb : d112688 q = 1) : d13133 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13134 q = 1) (hb : d112688 q = 1) : d114630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13134, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32724 (p : Pattern) (ha : d13002 p = 1) (hb : d112688 p = 1) : d114575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13001 q = 1) (hb : d112688 q = 1) : d114574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13002 q = 1) (hb : d112688 q = 1) : d114575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32725 (p : Pattern) (ha : d13011 p = 1) (hb : d112688 p = 1) : d114582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13009 q = 1) (hb : d112688 q = 1) : d114580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13010 q = 1) (hb : d112688 q = 1) : d114581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13010, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13011 q = 1) (hb : d112688 q = 1) : d114582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32726 (p : Pattern) (ha : d13036 p = 1) (hb : d112688 p = 1) : d114591 p = 1 := by
  have h0 (q : Pattern) (ha : d13021 q = 1) (hb : d94753 q = 1) : d13021 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12956 q = 1) (hb : d94753 q = 1) : d12956 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13030 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13031 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13031, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13032 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13032, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13033 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13033, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13034 q = 1) (hb : d112687 q = 1) : d114589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d112687, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13034, d112687, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13035 q = 1) (hb : d112688 q = 1) : d114590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d112688, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13035, d112688, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13036 q = 1) (hb : d112688 q = 1) : d114591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13036, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32727 (p : Pattern) (ha : d13046 p = 1) (hb : d112688 p = 1) : d114597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d112688 q = 1) : d114592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32726 q ha hb
    | true =>
      simp only [d13037, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d112688 q = 1) : d114593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32721 q ha hb
    | true =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d112688 q = 1) : d114594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d112688 q = 1) : d114595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d112688 q = 1) : d114596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d112688 q = 1) : d114597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32728 (p : Pattern) (ha : d13091 p = 1) (hb : d112688 p = 1) : d114603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d112688 q = 1) : d114600 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d112688 q = 1) : d114601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d112688 q = 1) : d114602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d112688 q = 1) : d114603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32729 (p : Pattern) (ha : d112688 p = 1) (hb : d115400 p = 1) : d114609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13004 q = 1) (hb : d112688 q = 1) : d13004 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13005 q = 1) (hb : d112688 q = 1) : d114576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32724 q ha hb
    | true =>
      simp only [d13005, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13006 q = 1) (hb : d112688 q = 1) : d114577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13007 q = 1) (hb : d112688 q = 1) : d114578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13007, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13008 q = 1) (hb : d112688 q = 1) : d114579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d112688 q = 1) : d13014 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13015 q = 1) (hb : d112688 q = 1) : d114583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32725 q ha hb
    | true =>
      simp only [d13015, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13016 q = 1) (hb : d112688 q = 1) : d114584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13017 q = 1) (hb : d112688 q = 1) : d114585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13017, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13051 q = 1) (hb : d112688 q = 1) : d114598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32727 q ha hb
    | true =>
      simp only [d13051, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32722 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115396 q = 1) : d114599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115396, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13092 q = 1) (hb : d112688 q = 1) : d114604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32728 q ha hb
    | true =>
      simp only [d13092, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13093 q = 1) (hb : d112688 q = 1) : d114605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13093, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115397 q = 1) : d114606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115397, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115398 q = 1) : d114607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115398, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115399 q = 1) : d114608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115399, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115400 q = 1) : d114609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115400, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32730 (p : Pattern) (ha : d13098 p = 1) (hb : d112688 p = 1) : d114610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13001 q = 1) (hb : d112688 q = 1) : d114574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13098 q = 1) (hb : d112688 q = 1) : d114610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13098, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32731 (p : Pattern) (ha : d13104 p = 1) (hb : d112688 p = 1) : d114615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13009 q = 1) (hb : d112688 q = 1) : d114580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13010 q = 1) (hb : d112688 q = 1) : d114581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13010, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13104 q = 1) (hb : d112688 q = 1) : d114615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13104, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32732 (p : Pattern) (ha : d13109 p = 1) (hb : d112688 p = 1) : d114619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d112688 q = 1) : d114592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32726 q ha hb
    | true =>
      simp only [d13037, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d112688 q = 1) : d114593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32721 q ha hb
    | true =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d112688 q = 1) : d114594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d112688 q = 1) : d114595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d112688 q = 1) : d114596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d112688 q = 1) : d114619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32733 (p : Pattern) (ha : d13110 p = 1) (hb : d112688 p = 1) : d114564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32721 q ha hb
    | true =>
      simp only [d13041, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13047 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13048 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13048, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13049 q = 1) (hb : d112688 q = 1) : d114554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13049, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13110 q = 1) (hb : d112688 q = 1) : d114564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13110, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32734 (p : Pattern) (ha : d13116 p = 1) (hb : d112688 p = 1) : d114622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32716 q ha hb
    | true =>
      simp only [d12968, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d112688 q = 1) : d114600 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d112688 q = 1) : d114601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d112688 q = 1) : d114602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d112688 q = 1) : d114622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32735 (p : Pattern) (ha : d112688 p = 1) (hb : d115405 p = 1) : d114628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13004 q = 1) (hb : d112688 q = 1) : d13004 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13005 q = 1) (hb : d112688 q = 1) : d114576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32724 q ha hb
    | true =>
      simp only [d13005, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13006 q = 1) (hb : d112688 q = 1) : d114577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13007 q = 1) (hb : d112688 q = 1) : d114578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13007, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13008 q = 1) (hb : d112688 q = 1) : d114579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d112688 q = 1) : d13014 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13015 q = 1) (hb : d112688 q = 1) : d114583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32725 q ha hb
    | true =>
      simp only [d13015, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13016 q = 1) (hb : d112688 q = 1) : d114584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13017 q = 1) (hb : d112688 q = 1) : d114585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13017, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13051 q = 1) (hb : d112688 q = 1) : d114598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32727 q ha hb
    | true =>
      simp only [d13051, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32722 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115396 q = 1) : d114599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115396, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13092 q = 1) (hb : d112688 q = 1) : d114604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32728 q ha hb
    | true =>
      simp only [d13092, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13093 q = 1) (hb : d112688 q = 1) : d114605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13093, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115397 q = 1) : d114606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115397, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115398 q = 1) : d114607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115398, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115399 q = 1) : d114608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115399, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13099 q = 1) (hb : d112688 q = 1) : d13099 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13100 q = 1) (hb : d112688 q = 1) : d114611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32730 q ha hb
    | true =>
      simp only [d13100, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13101 q = 1) (hb : d112688 q = 1) : d114612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d13102 q = 1) (hb : d112688 q = 1) : d114613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d13102, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d13103 q = 1) (hb : d112688 q = 1) : d114614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13105 q = 1) (hb : d112688 q = 1) : d13105 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d13106 q = 1) (hb : d112688 q = 1) : d114616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32731 q ha hb
    | true =>
      simp only [d13106, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d13107 q = 1) (hb : d112688 q = 1) : d114617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13108 q = 1) (hb : d112688 q = 1) : d114618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13108, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d13111 q = 1) (hb : d112688 q = 1) : d114620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32732 q ha hb
    | true =>
      simp only [d13111, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32733 q ha hb
  have h27 (q : Pattern) (ha : d112688 q = 1) (hb : d115401 q = 1) : d114621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d115401, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d13117 q = 1) (hb : d112688 q = 1) : d114623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32734 q ha hb
    | true =>
      simp only [d13117, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d13118 q = 1) (hb : d112688 q = 1) : d114624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d13118, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d112688 q = 1) (hb : d115402 q = 1) : d114625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115402, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d112688 q = 1) (hb : d115403 q = 1) : d114626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d115403, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d112688 q = 1) (hb : d115404 q = 1) : d114627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115404, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d112688 q = 1) (hb : d115405 q = 1) : d114628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115405, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro32736 (p : Pattern) (ha : d112688 p = 1) (hb : d115412 p = 1) : d114637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d112688 q = 1) : d114620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32732 q ha hb
    | true =>
      simp only [d13111, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32733 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115401 q = 1) : d114621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115401, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d112688 q = 1) : d114623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32734 q ha hb
    | true =>
      simp only [d13117, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d112688 q = 1) : d114624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115402 q = 1) : d114625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115410 q = 1) : d114635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115410, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115411 q = 1) : d114636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115411, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115412 q = 1) : d114637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115412, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32737 (p : Pattern) (ha : d13179 p = 1) (hb : d112688 p = 1) : d114648 p = 1 := by
  have h0 (q : Pattern) (ha : d13159 q = 1) (hb : d94753 q = 1) : d13159 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13156 q = 1) (hb : d94753 q = 1) : d13156 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13169 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13170 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13170, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13171 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13171, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13172 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13172, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13173 q = 1) (hb : d112687 q = 1) : d114646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d112687, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13173, d112687, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13177 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13178 q = 1) (hb : d112688 q = 1) : d114647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d112688, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13178, d112688, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13179 q = 1) (hb : d112688 q = 1) : d114648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13179, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32738 (p : Pattern) (ha : d13183 p = 1) (hb : d112688 p = 1) : d114653 p = 1 := by
  have h0 (q : Pattern) (ha : d13176 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6349 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6356, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d112687 q = 1) : d114651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d112687, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13177, d112687, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d6359 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13182 q = 1) (hb : d112688 q = 1) : d114652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d112688, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13182, d112688, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13183 q = 1) (hb : d112688 q = 1) : d114653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13183, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32739 (p : Pattern) (ha : d13189 p = 1) (hb : d112688 p = 1) : d114659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d112688 q = 1) : d114649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32737 q ha hb
    | true =>
      simp only [d13180, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d112688 q = 1) : d114650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32738 q ha hb
    | true =>
      simp only [d13184, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d112688 q = 1) : d114656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d112688 q = 1) : d114657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d112688 q = 1) : d114658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d112688 q = 1) : d114659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32740 (p : Pattern) (ha : d13202 p = 1) (hb : d112688 p = 1) : d114663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32738 q ha hb
    | true =>
      simp only [d13184, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13198 q = 1) (hb : d112688 q = 1) : d13198 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13199 q = 1) (hb : d112688 q = 1) : d114660 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13200 q = 1) (hb : d112688 q = 1) : d114661 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13200, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13201 q = 1) (hb : d112688 q = 1) : d114662 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13201, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13202 q = 1) (hb : d112688 q = 1) : d114663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13202, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32741 (p : Pattern) (ha : d13243 p = 1) (hb : d112688 p = 1) : d114653 p = 1 := by
  have h0 (q : Pattern) (ha : d13176 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6349 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6356, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d112687 q = 1) : d114651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d112687, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13177, d112687, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13194 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13242 q = 1) (hb : d112688 q = 1) : d114652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d112688, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13242, d112688, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13243 q = 1) (hb : d112688 q = 1) : d114653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13243, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32742 (p : Pattern) (ha : d13249 p = 1) (hb : d112688 p = 1) : d114669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32741 q ha hb
    | true =>
      simp only [d13244, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d112688 q = 1) : d114666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d112688 q = 1) : d114667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d112688 q = 1) : d114668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d112688 q = 1) : d114669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32743 (p : Pattern) (ha : d112688 p = 1) (hb : d115422 p = 1) : d114675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d112688 q = 1) : d114664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32739 q ha hb
    | true =>
      simp only [d13203, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32740 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115418 q = 1) : d114665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115418, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d112688 q = 1) : d114670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32742 q ha hb
    | true =>
      simp only [d13250, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d112688 q = 1) : d114671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115419 q = 1) : d114672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115420 q = 1) : d114673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115420, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115421 q = 1) : d114674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115421, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115422 q = 1) : d114675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115422, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32744 (p : Pattern) (ha : d112688 p = 1) (hb : d115428 p = 1) : d114681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d112688 q = 1) : d114562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32718 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d112688 q = 1) : d114563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d112688 q = 1) : d114571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32718 q ha hb
    | true =>
      simp only [d12998, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32720 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d112688 q = 1) : d114572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d112688 q = 1) : d114573 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115406 q = 1) : d114629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32729 q ha hb
    | true =>
      simp only [d115406, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32735 q ha hb
  have h7 (q : Pattern) (ha : d13140 q = 1) (hb : d112688 q = 1) : d13140 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13141 q = 1) (hb : d112688 q = 1) : d114631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32723 q ha hb
    | true =>
      simp only [d13141, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115407 q = 1) : d114632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115408 q = 1) : d114633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115408, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115409 q = 1) : d114634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115409, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115413 q = 1) : d114638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115413, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32736 q ha hb
  have h13 (q : Pattern) (ha : d13150 q = 1) (hb : d112688 q = 1) : d13150 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115414 q = 1) : d114639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115414, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115415 q = 1) : d114640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115415, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115416 q = 1) : d114641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115416, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115417 q = 1) : d114642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115417, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115423 q = 1) : d114676 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115423, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32743 q ha hb
  have h19 (q : Pattern) (ha : d13267 q = 1) (hb : d112688 q = 1) : d13267 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d112688 q = 1) (hb : d115424 q = 1) : d114677 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115424, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d112688 q = 1) (hb : d115425 q = 1) : d114678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115425, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112688 q = 1) (hb : d115426 q = 1) : d114679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115426, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112688 q = 1) (hb : d115427 q = 1) : d114680 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115427, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d112688 q = 1) (hb : d115428 q = 1) : d114681 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115428, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro32745 (p : Pattern) (ha : d112688 p = 1) (hb : d115434 p = 1) : d114687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115429 q = 1) : d114682 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115429, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32744 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115430 q = 1) : d114683 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115430, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115431 q = 1) : d114684 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115431, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115432 q = 1) : d114685 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115432, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115433 q = 1) : d114686 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115433, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115434 q = 1) : d114687 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115434, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32746 (p : Pattern) (ha : d13293 p = 1) (hb : d112688 p = 1) : d114693 p = 1 := by
  have h0 (q : Pattern) (ha : d13285 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5120 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5139 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5140, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d112687 q = 1) : d114691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d112687, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13286, d112687, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13291 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13292 q = 1) (hb : d112688 q = 1) : d114692 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d112688, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13292, d112688, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13293 q = 1) (hb : d112688 q = 1) : d114693 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13293, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32747 (p : Pattern) (ha : d13303 p = 1) (hb : d112688 p = 1) : d114699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13302 q = 1) (hb : d112688 q = 1) : d114698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13302, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13303 q = 1) (hb : d112688 q = 1) : d114699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32748 (p : Pattern) (ha : d13313 p = 1) (hb : d112688 p = 1) : d114705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13307 q = 1) (hb : d112688 q = 1) : d13307 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13308 q = 1) (hb : d112688 q = 1) : d114700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32747 q ha hb
    | true =>
      simp only [d13308, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13309 q = 1) (hb : d112688 q = 1) : d114701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13310 q = 1) (hb : d112688 q = 1) : d114702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13310, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13311 q = 1) (hb : d112688 q = 1) : d114703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13312 q = 1) (hb : d112688 q = 1) : d114704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13313 q = 1) (hb : d112688 q = 1) : d114705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32749 (p : Pattern) (ha : d13316 p = 1) (hb : d112688 p = 1) : d114708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13302 q = 1) (hb : d112688 q = 1) : d114698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13302, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13316 q = 1) (hb : d112688 q = 1) : d114708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13316, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
