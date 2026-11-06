import NetHack.Soko22Hazard87.AndIntroBlocks0075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro19000 (p : Pattern) (ha : d8658 p = 1) (hb : d81683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18988 q ha hb
    | true =>
      simp only [d6878, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d81672 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d81672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d81672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d81673 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d81673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d81673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d81674 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d81674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d81674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8658 q = 1) (hb : d81683 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, d81683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8658, d81683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19001 (p : Pattern) (ha : d8663 p = 1) (hb : d75885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18983 q ha hb
    | true =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d75873 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d75874 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d75874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d75874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d75875 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d75875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d75875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8663 q = 1) (hb : d75885 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d75885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8663, d75885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19002 (p : Pattern) (ha : d81689 p = 1) (hb : d94313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18991 q ha hb
    | true =>
      simp only [d8603, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18992 q ha hb
    | true =>
      simp only [d8610, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d81676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18994 q ha hb
    | true =>
      simp only [d8626, d81676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18989 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81677 q = 1) (hb : d94304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81677, d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81677, d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8642 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q ha hb
    | true =>
      simp only [d8642, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8643, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81678 q = 1) (hb : d94305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81678, d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81678, d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81679 q = 1) (hb : d94306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81679, d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81679, d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81680 q = 1) (hb : d94307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81680, d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81680, d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8649 q = 1) (hb : d52539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18997 q ha hb
    | true =>
      simp only [d8649, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q ha hb
  have h17 (q : Pattern) (ha : d8650 q = 1) (hb : d52540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8651 q = 1) (hb : d52541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d8651, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d8652 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8654 q = 1) (hb : d52545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18998 q ha hb
    | true =>
      simp only [d8654, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h21 (q : Pattern) (ha : d8655 q = 1) (hb : d52546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d8656 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d8656, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d8659 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18999 q ha hb
    | true =>
      simp only [d8659, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19000 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d81685 q = 1) (hb : d94309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81685, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d81685, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8664 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q ha hb
    | true =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8665 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d81686 q = 1) (hb : d94310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81686, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d81686, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d81687 q = 1) (hb : d94311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81687, d94311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d81687, d94311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d81688 q = 1) (hb : d94312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81688, d94312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d81688, d94312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d81689 q = 1) (hb : d94313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81689, d94313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81689, d94313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro19003 (p : Pattern) (ha : d81703 p = 1) (hb : d94320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18999 q ha hb
    | true =>
      simp only [d8659, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19000 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81685 q = 1) (hb : d94309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81685, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81685, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8664 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q ha hb
    | true =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8665 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81686 q = 1) (hb : d94310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81686, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81686, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81701 q = 1) (hb : d94318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81701, d94318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81701, d94318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81702 q = 1) (hb : d94319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81702, d94319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81702, d94319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81703 q = 1) (hb : d94320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81703, d94320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81703, d94320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19004 (p : Pattern) (ha : d8691 p = 1) (hb : d52611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8689 q = 1) (hb : d52604 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8689, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h7 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6921 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8690 q = 1) (hb : d52610 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8690, d52610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8690, d52610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8691 q = 1) (hb : d52611 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8691, d52611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8691, d52611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19005 (p : Pattern) (ha : d8697 p = 1) (hb : d81717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d52612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19004 q ha hb
    | true =>
      simp only [d8692, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d52613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6924 q = 1) (hb : d81712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d81712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11455 q ha hb
    | true =>
      simp only [d6924, d81712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d81713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d81713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d81713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8694 q = 1) (hb : d81714 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, d81714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8694, d81714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8695 q = 1) (hb : d81715 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, d81715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8695, d81715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8696 q = 1) (hb : d81716 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, d81716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8696, d81716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8697 q = 1) (hb : d81717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, d81717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8697, d81717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19006 (p : Pattern) (ha : d6923 p = 1) (hb : d75967 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6211 q = 1) (hb : d75962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
    | true =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h7 (q : Pattern) (ha : d6212 q = 1) (hb : d75963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6213 q = 1) (hb : d75964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6214 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6922 q = 1) (hb : d75966 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, d75966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6922, d75966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6923 q = 1) (hb : d75967 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, d75967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6923, d75967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19007 (p : Pattern) (ha : d8701 p = 1) (hb : d81721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d75968 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19006 q ha hb
    | true =>
      simp only [d6924, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d75969 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8698 q = 1) (hb : d81718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, d81718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8698, d81718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8699 q = 1) (hb : d81719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, d81719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8699, d81719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8700 q = 1) (hb : d81720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, d81720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8700, d81720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8701 q = 1) (hb : d81721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, d81721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8701, d81721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19008 (p : Pattern) (ha : d8715 p = 1) (hb : d52616 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h7 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8714 q = 1) (hb : d52615 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8714, d52615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8714, d52615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8715 q = 1) (hb : d52616 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8715, d52616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8715, d52616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19009 (p : Pattern) (ha : d8721 p = 1) (hb : d75978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19008 q ha hb
    | true =>
      simp only [d8716, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8718 q = 1) (hb : d75975 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d75975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d75975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8719 q = 1) (hb : d75976 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d75976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8719, d75976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8720 q = 1) (hb : d75977 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d75977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8720, d75977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8721 q = 1) (hb : d75978 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d75978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8721, d75978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19010 (p : Pattern) (ha : d81727 p = 1) (hb : d94330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d81722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, d81722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19005 q ha hb
    | true =>
      simp only [d8702, d81722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19007 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81723 q = 1) (hb : d94326 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81723, d94326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81723, d94326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8722 q = 1) (hb : d75981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19009 q ha hb
    | true =>
      simp only [d8722, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8723 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8723, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81724 q = 1) (hb : d94327 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81724, d94327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81724, d94327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81725 q = 1) (hb : d94328 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81725, d94328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81725, d94328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81726 q = 1) (hb : d94329 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81726, d94329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81726, d94329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81727 q = 1) (hb : d94330 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81727, d94330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81727, d94330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19011 (p : Pattern) (ha : d81733 p = 1) (hb : d94336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18985 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18985 q ha hb
    | true =>
      simp only [d8598, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18987 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81690 q = 1) (hb : d94314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81690, d94314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18996 q ha hb
    | true =>
      simp only [d81690, d94314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19002 q ha hb
  have h7 (q : Pattern) (ha : d8677 q = 1) (hb : d81697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, d81697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18990 q ha hb
    | true =>
      simp only [d8677, d81697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d81698 q = 1) (hb : d94315 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81698, d94315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81698, d94315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d81699 q = 1) (hb : d94316 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81699, d94316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d81699, d94316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d81700 q = 1) (hb : d94317 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81700, d94317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d81700, d94317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81704 q = 1) (hb : d94321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81704, d94321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81704, d94321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19003 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d81705 q = 1) (hb : d94322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81705, d94322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d81705, d94322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81706 q = 1) (hb : d94323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81706, d94323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81706, d94323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d81707 q = 1) (hb : d94324 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81707, d94324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d81707, d94324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d81708 q = 1) (hb : d94325 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81708, d94325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81708, d94325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d81728 q = 1) (hb : d94331 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81728, d94331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81728, d94331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19010 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d81729 q = 1) (hb : d94332 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81729, d94332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81729, d94332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d81730 q = 1) (hb : d94333 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81730, d94333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d81730, d94333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d81731 q = 1) (hb : d94334 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81731, d94334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d81731, d94334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d81732 q = 1) (hb : d94335 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81732, d94335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d81732, d94335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d81733 q = 1) (hb : d94336 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81733, d94336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81733, d94336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19012 (p : Pattern) (ha : d81739 p = 1) (hb : d94342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81734 q = 1) (hb : d94337 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81734, d94337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81734, d94337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19011 q ha hb
  have h2 (q : Pattern) (ha : d81735 q = 1) (hb : d94338 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81735, d94338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81735, d94338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81736 q = 1) (hb : d94339 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81736, d94339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81736, d94339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81737 q = 1) (hb : d94340 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81737, d94340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81737, d94340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81738 q = 1) (hb : d94341 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81738, d94341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81738, d94341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81739 q = 1) (hb : d94342 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81739, d94342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81739, d94342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19013 (p : Pattern) (ha : d8743 p = 1) (hb : d52729 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1142 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro155 q ha hb
  have h7 (q : Pattern) (ha : d1143 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1144 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1146 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1146, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8742 q = 1) (hb : d52728 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8742, d52728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8742, d52728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8743 q = 1) (hb : d52729 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8743, d52729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8743, d52729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19014 (p : Pattern) (ha : d8749 p = 1) (hb : d52739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8749 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, d52739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, d52739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19015 (p : Pattern) (ha : d8755 p = 1) (hb : d52749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19014 q ha hb
    | true =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8755 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19016 (p : Pattern) (ha : d8758 p = 1) (hb : d52752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8758 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, d52752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8758, d52752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19017 (p : Pattern) (ha : d8764 p = 1) (hb : d52759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19014 q ha hb
    | true =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8759 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19016 q ha hb
    | true =>
      simp only [d8759, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h7 (q : Pattern) (ha : d8760 q = 1) (hb : d52755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8761 q = 1) (hb : d52756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8761, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8762 q = 1) (hb : d52757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8763 q = 1) (hb : d52758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8764 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8764, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19018 (p : Pattern) (ha : d6956 p = 1) (hb : d69119 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5024 q = 1) (hb : d69114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d69114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
    | true =>
      simp only [d5024, d69114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7948 q ha hb
  have h7 (q : Pattern) (ha : d5025 q = 1) (hb : d69115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d69115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d69115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5026 q = 1) (hb : d69116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d69116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d69116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5027 q = 1) (hb : d69117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d69117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5027, d69117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6955 q = 1) (hb : d69118 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, d69118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6955, d69118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6956 q = 1) (hb : d69119 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, d69119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6956, d69119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19019 (p : Pattern) (ha : d8792 p = 1) (hb : d81754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19018 q ha hb
    | true =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d81751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d81751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d81751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d81752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d81752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d81752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d81753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d81753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d81753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8792 q = 1) (hb : d81754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, d81754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, d81754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19020 (p : Pattern) (ha : d8843 p = 1) (hb : d81775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8838 q = 1) (hb : d81770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, d81770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19019 q ha hb
    | true =>
      simp only [d8838, d81770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d8839 q = 1) (hb : d81771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, d81771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, d81771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8840 q = 1) (hb : d81772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, d81772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8840, d81772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8841 q = 1) (hb : d81773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, d81773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, d81773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8842 q = 1) (hb : d81774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, d81774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, d81774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8843 q = 1) (hb : d81775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, d81775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8843, d81775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19021 (p : Pattern) (ha : d8769 p = 1) (hb : d52764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8769 q = 1) (hb : d52764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, d52764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, d52764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19022 (p : Pattern) (ha : d8776 p = 1) (hb : d52773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8776 q = 1) (hb : d52773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, d52773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, d52773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19023 (p : Pattern) (ha : d8782 p = 1) (hb : d52802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8780 q = 1) (hb : d52800 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8780, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h7 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6954 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8781 q = 1) (hb : d52801 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8781, d52801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8781, d52801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8782 q = 1) (hb : d52802 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8782, d52802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8782, d52802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19024 (p : Pattern) (ha : d8788 p = 1) (hb : d81750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19023 q ha hb
    | true =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d81745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11470 q ha hb
    | true =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d81746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d81747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d81747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d81747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d81748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d81748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d81748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d81749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d81749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d81749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8788 q = 1) (hb : d81750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, d81750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, d81750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19025 (p : Pattern) (ha : d8808 p = 1) (hb : d76004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d76001 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d76002 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d76003 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d76003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d76003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8808 q = 1) (hb : d76004 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d76004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d76004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19026 (p : Pattern) (ha : d81760 p = 1) (hb : d94349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19021 q ha hb
    | true =>
      simp only [d8770, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19022 q ha hb
    | true =>
      simp only [d8777, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19024 q ha hb
    | true =>
      simp only [d8793, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19019 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81756 q = 1) (hb : d94345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81756, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81756, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8809 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q ha hb
    | true =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81757 q = 1) (hb : d94346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81757, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81757, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81758 q = 1) (hb : d94347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81758, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81758, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81759 q = 1) (hb : d94348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81759, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81759, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d81760 q = 1) (hb : d94349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81760, d94349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81760, d94349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro19027 (p : Pattern) (ha : d8815 p = 1) (hb : d52817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8815 q = 1) (hb : d52817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, d52817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8815, d52817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19028 (p : Pattern) (ha : d8820 p = 1) (hb : d52823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8820 q = 1) (hb : d52823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, d52823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8820, d52823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19029 (p : Pattern) (ha : d8824 p = 1) (hb : d81761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19023 q ha hb
    | true =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d81745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11470 q ha hb
    | true =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d81746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d81747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d81747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d81747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d81748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d81748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d81748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d81749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d81749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d81749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8824 q = 1) (hb : d81761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, d81761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8824, d81761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19030 (p : Pattern) (ha : d8825 p = 1) (hb : d81762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19018 q ha hb
    | true =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d81751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d81751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d81751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d81752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d81752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d81752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d81753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d81753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d81753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8825 q = 1) (hb : d81762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, d81762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8825, d81762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19031 (p : Pattern) (ha : d8830 p = 1) (hb : d76013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d76001 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d76002 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d76003 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d76003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d76003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8830 q = 1) (hb : d76013 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d76013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8830, d76013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19032 (p : Pattern) (ha : d81768 p = 1) (hb : d94354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19021 q ha hb
    | true =>
      simp only [d8770, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19022 q ha hb
    | true =>
      simp only [d8777, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19024 q ha hb
    | true =>
      simp only [d8793, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19019 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81756 q = 1) (hb : d94345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81756, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81756, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8809 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q ha hb
    | true =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81757 q = 1) (hb : d94346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81757, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81757, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81758 q = 1) (hb : d94347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81758, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81758, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81759 q = 1) (hb : d94348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81759, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81759, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8816 q = 1) (hb : d52819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19027 q ha hb
    | true =>
      simp only [d8816, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q ha hb
  have h17 (q : Pattern) (ha : d8817 q = 1) (hb : d52820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8818 q = 1) (hb : d52821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d8818, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d8819 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8821 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19028 q ha hb
    | true =>
      simp only [d8821, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h21 (q : Pattern) (ha : d8822 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d8823 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d8823, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d8826 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19029 q ha hb
    | true =>
      simp only [d8826, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19030 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d81764 q = 1) (hb : d94350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81764, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d81764, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8831 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q ha hb
    | true =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8832 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d81765 q = 1) (hb : d94351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81765, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d81765, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d81766 q = 1) (hb : d94352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81766, d94352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d81766, d94352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d81767 q = 1) (hb : d94353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81767, d94353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d81767, d94353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d81768 q = 1) (hb : d94354 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81768, d94354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81768, d94354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro19033 (p : Pattern) (ha : d81782 p = 1) (hb : d94361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19029 q ha hb
    | true =>
      simp only [d8826, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19030 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81764 q = 1) (hb : d94350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81764, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81764, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8831 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q ha hb
    | true =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8832 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81765 q = 1) (hb : d94351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81765, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81765, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81780 q = 1) (hb : d94359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81780, d94359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81780, d94359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81781 q = 1) (hb : d94360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81781, d94360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81781, d94360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81782 q = 1) (hb : d94361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81782, d94361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81782, d94361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19034 (p : Pattern) (ha : d8858 p = 1) (hb : d52905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8856 q = 1) (hb : d52893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8856, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h7 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7000 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8857 q = 1) (hb : d52904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8857, d52904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8857, d52904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8858 q = 1) (hb : d52905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8858, d52905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8858, d52905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19035 (p : Pattern) (ha : d8864 p = 1) (hb : d81796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d52906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19034 q ha hb
    | true =>
      simp only [d8859, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d52907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7003 q = 1) (hb : d81791 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d81791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11485 q ha hb
    | true =>
      simp only [d7003, d81791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d81792 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d81792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d81792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8861 q = 1) (hb : d81793 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, d81793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8861, d81793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8862 q = 1) (hb : d81794 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, d81794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8862, d81794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8863 q = 1) (hb : d81795 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, d81795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8863, d81795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8864 q = 1) (hb : d81796 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, d81796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8864, d81796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19036 (p : Pattern) (ha : d7002 p = 1) (hb : d76101 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6356 q = 1) (hb : d76096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d76096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
    | true =>
      simp only [d6356, d76096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q ha hb
  have h7 (q : Pattern) (ha : d6357 q = 1) (hb : d76097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d76097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d76097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6358 q = 1) (hb : d76098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d76098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d76098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6359 q = 1) (hb : d76099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d76099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6359, d76099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7001 q = 1) (hb : d76100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, d76100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7001, d76100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7002 q = 1) (hb : d76101 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, d76101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7002, d76101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19037 (p : Pattern) (ha : d8868 p = 1) (hb : d81800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d76102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19036 q ha hb
    | true =>
      simp only [d7003, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d76103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8865 q = 1) (hb : d81797 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, d81797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8865, d81797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8866 q = 1) (hb : d81798 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, d81798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8866, d81798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8867 q = 1) (hb : d81799 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, d81799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8867, d81799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8868 q = 1) (hb : d81800 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, d81800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8868, d81800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19038 (p : Pattern) (ha : d8882 p = 1) (hb : d52910 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1412 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro168 q ha hb
  have h7 (q : Pattern) (ha : d1413 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1414 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1420 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1420, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8881 q = 1) (hb : d52909 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, d52909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8881, d52909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8882 q = 1) (hb : d52910 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, d52910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8882, d52910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19039 (p : Pattern) (ha : d8888 p = 1) (hb : d76112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19038 q ha hb
    | true =>
      simp only [d8883, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8885 q = 1) (hb : d76109 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d76109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d76109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8886 q = 1) (hb : d76110 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d76110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8886, d76110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8887 q = 1) (hb : d76111 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d76111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8887, d76111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8888 q = 1) (hb : d76112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d76112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8888, d76112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19040 (p : Pattern) (ha : d81806 p = 1) (hb : d94371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d81801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, d81801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19035 q ha hb
    | true =>
      simp only [d8869, d81801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19037 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81802 q = 1) (hb : d94367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81802, d94367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81802, d94367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8889 q = 1) (hb : d76115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19039 q ha hb
    | true =>
      simp only [d8889, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8890 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8890, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81803 q = 1) (hb : d94368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81803, d94368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81803, d94368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81804 q = 1) (hb : d94369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81804, d94369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81804, d94369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81805 q = 1) (hb : d94370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81805, d94370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81805, d94370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81806 q = 1) (hb : d94371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81806, d94371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81806, d94371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19041 (p : Pattern) (ha : d81812 p = 1) (hb : d94377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19015 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19015 q ha hb
    | true =>
      simp only [d8765, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19017 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81769 q = 1) (hb : d94355 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81769, d94355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19026 q ha hb
    | true =>
      simp only [d81769, d94355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19032 q ha hb
  have h7 (q : Pattern) (ha : d8844 q = 1) (hb : d81776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, d81776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19020 q ha hb
    | true =>
      simp only [d8844, d81776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d81777 q = 1) (hb : d94356 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81777, d94356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81777, d94356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d81778 q = 1) (hb : d94357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81778, d94357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d81778, d94357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d81779 q = 1) (hb : d94358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81779, d94358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d81779, d94358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81783 q = 1) (hb : d94362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81783, d94362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81783, d94362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19033 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d81784 q = 1) (hb : d94363 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81784, d94363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d81784, d94363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81785 q = 1) (hb : d94364 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81785, d94364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81785, d94364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d81786 q = 1) (hb : d94365 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81786, d94365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d81786, d94365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d81787 q = 1) (hb : d94366 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81787, d94366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81787, d94366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d81807 q = 1) (hb : d94372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81807, d94372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81807, d94372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19040 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d81808 q = 1) (hb : d94373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81808, d94373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81808, d94373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d81809 q = 1) (hb : d94374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81809, d94374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d81809, d94374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d81810 q = 1) (hb : d94375 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81810, d94375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d81810, d94375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d81811 q = 1) (hb : d94376 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81811, d94376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d81811, d94376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d81812 q = 1) (hb : d94377 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81812, d94377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81812, d94377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19042 (p : Pattern) (ha : d81818 p = 1) (hb : d94383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81813 q = 1) (hb : d94378 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81813, d94378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81813, d94378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19041 q ha hb
  have h2 (q : Pattern) (ha : d81814 q = 1) (hb : d94379 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81814, d94379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81814, d94379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81815 q = 1) (hb : d94380 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81815, d94380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81815, d94380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81816 q = 1) (hb : d94381 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81816, d94381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81816, d94381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81817 q = 1) (hb : d94382 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81817, d94382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81817, d94382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81818 q = 1) (hb : d94383 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81818, d94383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81818, d94383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19043 (p : Pattern) (ha : d8911 p = 1) (hb : d53050 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1603 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro213 q ha hb
  have h7 (q : Pattern) (ha : d1604 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1605 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1607 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1607, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8910 q = 1) (hb : d53049 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, d53049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8910, d53049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8911 q = 1) (hb : d53050 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, d53050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8911, d53050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19044 (p : Pattern) (ha : d8917 p = 1) (hb : d53060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8917 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, d53060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, d53060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19045 (p : Pattern) (ha : d8923 p = 1) (hb : d53070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19044 q ha hb
    | true =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8923 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19046 (p : Pattern) (ha : d8926 p = 1) (hb : d53073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8926 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, d53073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8926, d53073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19047 (p : Pattern) (ha : d8932 p = 1) (hb : d53080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19044 q ha hb
    | true =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8927 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19046 q ha hb
    | true =>
      simp only [d8927, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h7 (q : Pattern) (ha : d8928 q = 1) (hb : d53076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8929 q = 1) (hb : d53077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8929, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8930 q = 1) (hb : d53078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8931 q = 1) (hb : d53079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8932 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8932, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19048 (p : Pattern) (ha : d7036 p = 1) (hb : d69232 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5140 q = 1) (hb : d69227 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d69227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
    | true =>
      simp only [d5140, d69227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7965 q ha hb
  have h7 (q : Pattern) (ha : d5141 q = 1) (hb : d69228 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d69228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d69228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5142 q = 1) (hb : d69229 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d69229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d69229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5143 q = 1) (hb : d69230 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d69230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5143, d69230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7035 q = 1) (hb : d69231 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, d69231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7035, d69231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7036 q = 1) (hb : d69232 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, d69232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7036, d69232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19049 (p : Pattern) (ha : d8960 p = 1) (hb : d81834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19048 q ha hb
    | true =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d81831 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d81831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d81831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d81832 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d81832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d81832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d81833 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d81833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d81833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8960 q = 1) (hb : d81834 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, d81834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, d81834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19050 (p : Pattern) (ha : d9011 p = 1) (hb : d81855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9006 q = 1) (hb : d81850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, d81850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19049 q ha hb
    | true =>
      simp only [d9006, d81850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d9007 q = 1) (hb : d81851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, d81851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, d81851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9008 q = 1) (hb : d81852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, d81852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9008, d81852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9009 q = 1) (hb : d81853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, d81853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, d81853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9010 q = 1) (hb : d81854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, d81854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, d81854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9011 q = 1) (hb : d81855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, d81855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9011, d81855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19051 (p : Pattern) (ha : d8937 p = 1) (hb : d53085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8937 q = 1) (hb : d53085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, d53085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, d53085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19052 (p : Pattern) (ha : d8944 p = 1) (hb : d53094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8944 q = 1) (hb : d53094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, d53094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, d53094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19053 (p : Pattern) (ha : d8950 p = 1) (hb : d53117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8948 q = 1) (hb : d53115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8948, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h7 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7034 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8949 q = 1) (hb : d53116 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, d53116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8949, d53116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8950 q = 1) (hb : d53117 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, d53117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8950, d53117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19054 (p : Pattern) (ha : d8956 p = 1) (hb : d81830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19053 q ha hb
    | true =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d81825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11500 q ha hb
    | true =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d81826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d81827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d81827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d81827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d81828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d81828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d81828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d81829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d81829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d81829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8956 q = 1) (hb : d81830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, d81830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, d81830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19055 (p : Pattern) (ha : d8976 p = 1) (hb : d76139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d76136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d76137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d76138 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d76138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d76138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8976 q = 1) (hb : d76139 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d76139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d76139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19056 (p : Pattern) (ha : d81840 p = 1) (hb : d94391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19051 q ha hb
    | true =>
      simp only [d8938, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19052 q ha hb
    | true =>
      simp only [d8945, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19054 q ha hb
    | true =>
      simp only [d8961, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19049 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81836 q = 1) (hb : d94387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81836, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81836, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8977 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q ha hb
    | true =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81837 q = 1) (hb : d94388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81837, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81837, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81838 q = 1) (hb : d94389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81838, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81838, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81839 q = 1) (hb : d94390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81839, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81839, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d81840 q = 1) (hb : d94391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81840, d94391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81840, d94391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro19057 (p : Pattern) (ha : d8983 p = 1) (hb : d53132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8983 q = 1) (hb : d53132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, d53132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8983, d53132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19058 (p : Pattern) (ha : d8988 p = 1) (hb : d53138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8988 q = 1) (hb : d53138 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, d53138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8988, d53138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19059 (p : Pattern) (ha : d8992 p = 1) (hb : d81841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19053 q ha hb
    | true =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d81825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11500 q ha hb
    | true =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d81826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d81827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d81827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d81827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d81828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d81828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d81828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d81829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d81829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d81829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8992 q = 1) (hb : d81841 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, d81841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8992, d81841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19060 (p : Pattern) (ha : d8993 p = 1) (hb : d81842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19048 q ha hb
    | true =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d81831 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d81831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d81831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d81832 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d81832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d81832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d81833 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d81833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d81833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8993 q = 1) (hb : d81842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, d81842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8993, d81842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19061 (p : Pattern) (ha : d8998 p = 1) (hb : d76148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d76136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d76137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d76138 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d76138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d76138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8998 q = 1) (hb : d76148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d76148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8998, d76148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19062 (p : Pattern) (ha : d81848 p = 1) (hb : d94396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19051 q ha hb
    | true =>
      simp only [d8938, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19052 q ha hb
    | true =>
      simp only [d8945, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19054 q ha hb
    | true =>
      simp only [d8961, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19049 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81836 q = 1) (hb : d94387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81836, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81836, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8977 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q ha hb
    | true =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81837 q = 1) (hb : d94388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81837, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81837, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81838 q = 1) (hb : d94389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81838, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81838, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81839 q = 1) (hb : d94390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81839, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81839, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8984 q = 1) (hb : d53134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19057 q ha hb
    | true =>
      simp only [d8984, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q ha hb
  have h17 (q : Pattern) (ha : d8985 q = 1) (hb : d53135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8986 q = 1) (hb : d53136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d8986, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d8987 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8989 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19058 q ha hb
    | true =>
      simp only [d8989, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h21 (q : Pattern) (ha : d8990 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d8991 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d8991, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d8994 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19059 q ha hb
    | true =>
      simp only [d8994, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19060 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d81844 q = 1) (hb : d94392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81844, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d81844, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8999 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q ha hb
    | true =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9000 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d81845 q = 1) (hb : d94393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81845, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d81845, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d81846 q = 1) (hb : d94394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81846, d94394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d81846, d94394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d81847 q = 1) (hb : d94395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81847, d94395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d81847, d94395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d81848 q = 1) (hb : d94396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81848, d94396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81848, d94396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro19063 (p : Pattern) (ha : d81862 p = 1) (hb : d94403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19059 q ha hb
    | true =>
      simp only [d8994, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19060 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81844 q = 1) (hb : d94392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81844, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81844, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8999 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q ha hb
    | true =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9000 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81845 q = 1) (hb : d94393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81845, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81845, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81860 q = 1) (hb : d94401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81860, d94401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81860, d94401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81861 q = 1) (hb : d94402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81861, d94402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81861, d94402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81862 q = 1) (hb : d94403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81862, d94403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81862, d94403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19064 (p : Pattern) (ha : d9026 p = 1) (hb : d53220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9024 q = 1) (hb : d53208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9024, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h7 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7080 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9025 q = 1) (hb : d53219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, d53219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9025, d53219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9026 q = 1) (hb : d53220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, d53220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9026, d53220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19065 (p : Pattern) (ha : d9032 p = 1) (hb : d81876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d53221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19064 q ha hb
    | true =>
      simp only [d9027, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d53222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7083 q = 1) (hb : d81871 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d81871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11515 q ha hb
    | true =>
      simp only [d7083, d81871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d81872 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d81872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d81872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9029 q = 1) (hb : d81873 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, d81873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9029, d81873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9030 q = 1) (hb : d81874 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, d81874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9030, d81874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9031 q = 1) (hb : d81875 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, d81875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9031, d81875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9032 q = 1) (hb : d81876 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, d81876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9032, d81876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19066 (p : Pattern) (ha : d7082 p = 1) (hb : d76236 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6502 q = 1) (hb : d76231 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d76231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
    | true =>
      simp only [d6502, d76231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q ha hb
  have h7 (q : Pattern) (ha : d6503 q = 1) (hb : d76232 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d76232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d76232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6504 q = 1) (hb : d76233 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d76233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d76233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6505 q = 1) (hb : d76234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d76234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6505, d76234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7081 q = 1) (hb : d76235 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, d76235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7081, d76235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7082 q = 1) (hb : d76236 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, d76236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7082, d76236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19067 (p : Pattern) (ha : d9036 p = 1) (hb : d81880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d76237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19066 q ha hb
    | true =>
      simp only [d7083, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d76238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9033 q = 1) (hb : d81877 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, d81877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9033, d81877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9034 q = 1) (hb : d81878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, d81878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9034, d81878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9035 q = 1) (hb : d81879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, d81879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9035, d81879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9036 q = 1) (hb : d81880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, d81880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9036, d81880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19068 (p : Pattern) (ha : d9050 p = 1) (hb : d53225 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1889 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro226 q ha hb
  have h7 (q : Pattern) (ha : d1890 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1891 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1897 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1897, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9049 q = 1) (hb : d53224 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, d53224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9049, d53224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9050 q = 1) (hb : d53225 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, d53225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9050, d53225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19069 (p : Pattern) (ha : d9056 p = 1) (hb : d76247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19068 q ha hb
    | true =>
      simp only [d9051, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9053 q = 1) (hb : d76244 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d76244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d76244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9054 q = 1) (hb : d76245 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d76245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9054, d76245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9055 q = 1) (hb : d76246 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d76246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9055, d76246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9056 q = 1) (hb : d76247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d76247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9056, d76247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19070 (p : Pattern) (ha : d81886 p = 1) (hb : d94413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d81881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, d81881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19065 q ha hb
    | true =>
      simp only [d9037, d81881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19067 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81882 q = 1) (hb : d94409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81882, d94409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81882, d94409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9057 q = 1) (hb : d76250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19069 q ha hb
    | true =>
      simp only [d9057, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9058 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9058, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81883 q = 1) (hb : d94410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81883, d94410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81883, d94410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81884 q = 1) (hb : d94411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81884, d94411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81884, d94411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81885 q = 1) (hb : d94412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81885, d94412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81885, d94412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81886 q = 1) (hb : d94413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81886, d94413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81886, d94413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19071 (p : Pattern) (ha : d81892 p = 1) (hb : d94419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19045 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19045 q ha hb
    | true =>
      simp only [d8933, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19047 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81849 q = 1) (hb : d94397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81849, d94397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19056 q ha hb
    | true =>
      simp only [d81849, d94397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19062 q ha hb
  have h7 (q : Pattern) (ha : d9012 q = 1) (hb : d81856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, d81856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19050 q ha hb
    | true =>
      simp only [d9012, d81856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d81857 q = 1) (hb : d94398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81857, d94398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81857, d94398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d81858 q = 1) (hb : d94399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81858, d94399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d81858, d94399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d81859 q = 1) (hb : d94400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81859, d94400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d81859, d94400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81863 q = 1) (hb : d94404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81863, d94404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81863, d94404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19063 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d81864 q = 1) (hb : d94405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81864, d94405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d81864, d94405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81865 q = 1) (hb : d94406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81865, d94406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81865, d94406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d81866 q = 1) (hb : d94407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81866, d94407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d81866, d94407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d81867 q = 1) (hb : d94408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81867, d94408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81867, d94408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d81887 q = 1) (hb : d94414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81887, d94414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81887, d94414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19070 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d81888 q = 1) (hb : d94415 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81888, d94415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81888, d94415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d81889 q = 1) (hb : d94416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81889, d94416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d81889, d94416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d81890 q = 1) (hb : d94417 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81890, d94417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d81890, d94417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d81891 q = 1) (hb : d94418 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81891, d94418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d81891, d94418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d81892 q = 1) (hb : d94419 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81892, d94419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81892, d94419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19072 (p : Pattern) (ha : d81898 p = 1) (hb : d94425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81893 q = 1) (hb : d94420 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81893, d94420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81893, d94420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19071 q ha hb
  have h2 (q : Pattern) (ha : d81894 q = 1) (hb : d94421 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81894, d94421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81894, d94421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81895 q = 1) (hb : d94422 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81895, d94422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81895, d94422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81896 q = 1) (hb : d94423 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81896, d94423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81896, d94423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81897 q = 1) (hb : d94424 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81897, d94424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81897, d94424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81898 q = 1) (hb : d94425 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81898, d94425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81898, d94425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19073 (p : Pattern) (ha : d9080 p = 1) (hb : d53371 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2086 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro272 q ha hb
  have h7 (q : Pattern) (ha : d2087 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2088 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2090 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2090, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9079 q = 1) (hb : d53370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9079, d53370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9079, d53370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9080 q = 1) (hb : d53371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9080, d53371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9080, d53371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19074 (p : Pattern) (ha : d9086 p = 1) (hb : d53381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9085 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9085, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9086 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9086, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19075 (p : Pattern) (ha : d9092 p = 1) (hb : d53391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19074 q ha hb
    | true =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9092 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19076 (p : Pattern) (ha : d9095 p = 1) (hb : d53394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9085 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9085, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9095 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9095, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19077 (p : Pattern) (ha : d9101 p = 1) (hb : d53401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19074 q ha hb
    | true =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9096 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19076 q ha hb
    | true =>
      simp only [d9096, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h7 (q : Pattern) (ha : d9097 q = 1) (hb : d53397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9098 q = 1) (hb : d53398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9098, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9099 q = 1) (hb : d53399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9100 q = 1) (hb : d53400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9101 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9101, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19078 (p : Pattern) (ha : d7117 p = 1) (hb : d69342 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5253 q = 1) (hb : d69337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d69337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q ha hb
    | true =>
      simp only [d5253, d69337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7981 q ha hb
  have h7 (q : Pattern) (ha : d5254 q = 1) (hb : d69338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d69338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d69338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5255 q = 1) (hb : d69339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d69339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d69339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5256 q = 1) (hb : d69340 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d69340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5256, d69340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7116 q = 1) (hb : d69341 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7116, d69341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7116, d69341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7117 q = 1) (hb : d69342 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7117, d69342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7117, d69342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19079 (p : Pattern) (ha : d9129 p = 1) (hb : d81915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19078 q ha hb
    | true =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d81912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9127 q = 1) (hb : d81913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9128 q = 1) (hb : d81914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9128, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9129 q = 1) (hb : d81915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, d81915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9129, d81915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19080 (p : Pattern) (ha : d9180 p = 1) (hb : d81936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9175 q = 1) (hb : d81931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, d81931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19079 q ha hb
    | true =>
      simp only [d9175, d81931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d9176 q = 1) (hb : d81932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, d81932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9176, d81932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9177 q = 1) (hb : d81933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, d81933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9177, d81933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9178 q = 1) (hb : d81934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, d81934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9178, d81934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9179 q = 1) (hb : d81935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, d81935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9179, d81935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9180 q = 1) (hb : d81936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, d81936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9180, d81936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19081 (p : Pattern) (ha : d9106 p = 1) (hb : d53406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9105 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9106 q = 1) (hb : d53406 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9106, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19082 (p : Pattern) (ha : d9113 p = 1) (hb : d53415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9111 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9112 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9112, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9113 q = 1) (hb : d53415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9113, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19083 (p : Pattern) (ha : d9119 p = 1) (hb : d53434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9117 q = 1) (hb : d53432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9117, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h7 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7115 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9118 q = 1) (hb : d53433 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9118, d53433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9118, d53433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9119 q = 1) (hb : d53434 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9119, d53434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9119, d53434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19084 (p : Pattern) (ha : d9125 p = 1) (hb : d81911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19083 q ha hb
    | true =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d81906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11530 q ha hb
    | true =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d81908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d81909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d81910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9125 q = 1) (hb : d81911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, d81911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9125, d81911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19085 (p : Pattern) (ha : d9145 p = 1) (hb : d76275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d76272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d76273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d76274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d76274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d76274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9145 q = 1) (hb : d76275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, d76275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, d76275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19086 (p : Pattern) (ha : d81921 p = 1) (hb : d94434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19081 q ha hb
    | true =>
      simp only [d9107, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19082 q ha hb
    | true =>
      simp only [d9114, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19084 q ha hb
    | true =>
      simp only [d9130, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19079 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81917 q = 1) (hb : d94430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81917, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81917, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9146 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q ha hb
    | true =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81918 q = 1) (hb : d94431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81918, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81918, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81919 q = 1) (hb : d94432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81919, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81919, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81920 q = 1) (hb : d94433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81920, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81920, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d81921 q = 1) (hb : d94434 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81921, d94434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81921, d94434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro19087 (p : Pattern) (ha : d9152 p = 1) (hb : d53449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9105 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9152 q = 1) (hb : d53449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9152, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19088 (p : Pattern) (ha : d9157 p = 1) (hb : d53455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9111 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9112 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9112, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9157 q = 1) (hb : d53455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9157, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19089 (p : Pattern) (ha : d9161 p = 1) (hb : d81922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19083 q ha hb
    | true =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d81906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11530 q ha hb
    | true =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d81908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d81909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d81910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9161 q = 1) (hb : d81922 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, d81922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9161, d81922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19090 (p : Pattern) (ha : d9162 p = 1) (hb : d81923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19078 q ha hb
    | true =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d81912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9127 q = 1) (hb : d81913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9128 q = 1) (hb : d81914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9128, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9162 q = 1) (hb : d81923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, d81923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9162, d81923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19091 (p : Pattern) (ha : d9167 p = 1) (hb : d76284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d76272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d76273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d76274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d76274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d76274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9167 q = 1) (hb : d76284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, d76284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9167, d76284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19092 (p : Pattern) (ha : d81929 p = 1) (hb : d94439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19081 q ha hb
    | true =>
      simp only [d9107, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19082 q ha hb
    | true =>
      simp only [d9114, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19084 q ha hb
    | true =>
      simp only [d9130, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19079 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d81917 q = 1) (hb : d94430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81917, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d81917, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9146 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q ha hb
    | true =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d81918 q = 1) (hb : d94431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81918, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81918, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81919 q = 1) (hb : d94432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81919, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81919, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81920 q = 1) (hb : d94433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81920, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81920, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9153 q = 1) (hb : d53451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19087 q ha hb
    | true =>
      simp only [d9153, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q ha hb
  have h17 (q : Pattern) (ha : d9154 q = 1) (hb : d53452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9154, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9155 q = 1) (hb : d53453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9155, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9156 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9156, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9158 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19088 q ha hb
    | true =>
      simp only [d9158, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h21 (q : Pattern) (ha : d9159 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9159, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9160 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9160, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d9163 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19089 q ha hb
    | true =>
      simp only [d9163, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19090 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d81925 q = 1) (hb : d94435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81925, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d81925, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9168 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q ha hb
    | true =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9169 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d81926 q = 1) (hb : d94436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81926, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d81926, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d81927 q = 1) (hb : d94437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81927, d94437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d81927, d94437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d81928 q = 1) (hb : d94438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81928, d94438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d81928, d94438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d81929 q = 1) (hb : d94439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81929, d94439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81929, d94439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro19093 (p : Pattern) (ha : d81943 p = 1) (hb : d94446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9163 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19089 q ha hb
    | true =>
      simp only [d9163, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19090 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81925 q = 1) (hb : d94435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81925, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81925, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9168 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q ha hb
    | true =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9169 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81926 q = 1) (hb : d94436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81926, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81926, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81941 q = 1) (hb : d94444 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81941, d94444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81941, d94444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81942 q = 1) (hb : d94445 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81942, d94445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81942, d94445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81943 q = 1) (hb : d94446 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81943, d94446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81943, d94446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19094 (p : Pattern) (ha : d9195 p = 1) (hb : d53537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9193 q = 1) (hb : d53525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9193, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h7 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7161 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9194 q = 1) (hb : d53536 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9194, d53536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9194, d53536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9195 q = 1) (hb : d53537 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9195, d53537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9195, d53537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro19095 (p : Pattern) (ha : d9201 p = 1) (hb : d81957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9196 q = 1) (hb : d53538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19094 q ha hb
    | true =>
      simp only [d9196, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d53539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7164 q = 1) (hb : d81952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d81952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11545 q ha hb
    | true =>
      simp only [d7164, d81952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d81953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d81953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d81953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9198 q = 1) (hb : d81954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, d81954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9198, d81954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9199 q = 1) (hb : d81955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, d81955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9199, d81955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9200 q = 1) (hb : d81956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, d81956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9200, d81956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9201 q = 1) (hb : d81957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, d81957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9201, d81957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19096 (p : Pattern) (ha : d7163 p = 1) (hb : d76372 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6649 q = 1) (hb : d76367 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d76367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q ha hb
    | true =>
      simp only [d6649, d76367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q ha hb
  have h7 (q : Pattern) (ha : d6650 q = 1) (hb : d76368 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d76368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d76368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6651 q = 1) (hb : d76369 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d76369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d76369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6652 q = 1) (hb : d76370 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d76370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6652, d76370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7162 q = 1) (hb : d76371 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7162, d76371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7162, d76371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7163 q = 1) (hb : d76372 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7163, d76372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7163, d76372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19097 (p : Pattern) (ha : d9205 p = 1) (hb : d81961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7164 q = 1) (hb : d76373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19096 q ha hb
    | true =>
      simp only [d7164, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d76374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9202 q = 1) (hb : d81958 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, d81958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9202, d81958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9203 q = 1) (hb : d81959 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, d81959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9203, d81959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9204 q = 1) (hb : d81960 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, d81960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9204, d81960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9205 q = 1) (hb : d81961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, d81961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9205, d81961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19098 (p : Pattern) (ha : d9219 p = 1) (hb : d53542 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2367 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro285 q ha hb
  have h7 (q : Pattern) (ha : d2368 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2369 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2375 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2375, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9218 q = 1) (hb : d53541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9218, d53541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9218, d53541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9219 q = 1) (hb : d53542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9219, d53542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9219, d53542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro19099 (p : Pattern) (ha : d9225 p = 1) (hb : d76383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19098 q ha hb
    | true =>
      simp only [d9220, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9222 q = 1) (hb : d76380 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, d76380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, d76380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9223 q = 1) (hb : d76381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, d76381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9223, d76381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9224 q = 1) (hb : d76382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, d76382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9224, d76382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9225 q = 1) (hb : d76383 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, d76383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9225, d76383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19100 (p : Pattern) (ha : d81967 p = 1) (hb : d94456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9206 q = 1) (hb : d81962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, d81962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19095 q ha hb
    | true =>
      simp only [d9206, d81962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19097 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d81963 q = 1) (hb : d94452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81963, d94452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81963, d94452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9226 q = 1) (hb : d76386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19099 q ha hb
    | true =>
      simp only [d9226, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9227 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9227, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d81964 q = 1) (hb : d94453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81964, d94453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81964, d94453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81965 q = 1) (hb : d94454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81965, d94454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81965, d94454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81966 q = 1) (hb : d94455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81966, d94455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81966, d94455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81967 q = 1) (hb : d94456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81967, d94456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81967, d94456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19101 (p : Pattern) (ha : d81973 p = 1) (hb : d94462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9093 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9093, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19075 q ha hb
  have h2 (q : Pattern) (ha : d9094 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9094, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9102 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19075 q ha hb
    | true =>
      simp only [d9102, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19077 q ha hb
  have h4 (q : Pattern) (ha : d9103 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9103, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9104 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9104, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81930 q = 1) (hb : d94440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81930, d94440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19086 q ha hb
    | true =>
      simp only [d81930, d94440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19092 q ha hb
  have h7 (q : Pattern) (ha : d9181 q = 1) (hb : d81937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, d81937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19080 q ha hb
    | true =>
      simp only [d9181, d81937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d81938 q = 1) (hb : d94441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81938, d94441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81938, d94441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d81939 q = 1) (hb : d94442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81939, d94442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d81939, d94442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d81940 q = 1) (hb : d94443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81940, d94443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d81940, d94443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81944 q = 1) (hb : d94447 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81944, d94447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81944, d94447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19093 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d81945 q = 1) (hb : d94448 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81945, d94448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d81945, d94448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d81946 q = 1) (hb : d94449 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81946, d94449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81946, d94449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d81947 q = 1) (hb : d94450 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81947, d94450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d81947, d94450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d81948 q = 1) (hb : d94451 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81948, d94451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81948, d94451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d81968 q = 1) (hb : d94457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81968, d94457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81968, d94457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19100 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d81969 q = 1) (hb : d94458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81969, d94458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81969, d94458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d81970 q = 1) (hb : d94459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81970, d94459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d81970, d94459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d81971 q = 1) (hb : d94460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81971, d94460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d81971, d94460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d81972 q = 1) (hb : d94461 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81972, d94461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d81972, d94461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d81973 q = 1) (hb : d94462 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81973, d94462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81973, d94462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro19102 (p : Pattern) (ha : d81979 p = 1) (hb : d94468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81974 q = 1) (hb : d94463 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81974, d94463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81974, d94463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19101 q ha hb
  have h2 (q : Pattern) (ha : d81975 q = 1) (hb : d94464 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81975, d94464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81975, d94464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81976 q = 1) (hb : d94465 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81976, d94465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81976, d94465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81977 q = 1) (hb : d94466 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81977, d94466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81977, d94466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81978 q = 1) (hb : d94467 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81978, d94467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81978, d94467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81979 q = 1) (hb : d94468 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81979, d94468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81979, d94468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19103 (p : Pattern) (ha : d81985 p = 1) (hb : d94474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d81662 q = 1) (hb : d94303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81662, d94303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18952 q ha hb
    | true =>
      simp only [d81662, d94303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18982 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d81740 q = 1) (hb : d94343 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81740, d94343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81740, d94343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19012 q ha hb
  have h3 (q : Pattern) (ha : d81741 q = 1) (hb : d94344 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81741, d94344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d81741, d94344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81819 q = 1) (hb : d94384 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81819, d94384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81819, d94384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19042 q ha hb
  have h5 (q : Pattern) (ha : d81820 q = 1) (hb : d94385 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81820, d94385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81820, d94385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81821 q = 1) (hb : d94386 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81821, d94386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81821, d94386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81899 q = 1) (hb : d94426 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81899, d94426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81899, d94426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19072 q ha hb
  have h8 (q : Pattern) (ha : d81900 q = 1) (hb : d94427 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81900, d94427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81900, d94427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81901 q = 1) (hb : d94428 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81901, d94428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81901, d94428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81902 q = 1) (hb : d94429 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d81902, d94429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81902, d94429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81980 q = 1) (hb : d94469 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81980, d94469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81980, d94469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19102 q ha hb
  have h12 (q : Pattern) (ha : d81981 q = 1) (hb : d94470 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81981, d94470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81981, d94470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81982 q = 1) (hb : d94471 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81982, d94471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81982, d94471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d81983 q = 1) (hb : d94472 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d81983, d94472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81983, d94472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81984 q = 1) (hb : d94473 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d81984, d94473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81984, d94473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d81985 q = 1) (hb : d94474 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d81985, d94474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81985, d94474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro19104 (p : Pattern) (ha : d81991 p = 1) (hb : d94480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81986 q = 1) (hb : d94475 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d81986, d94475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19103 q ha hb
    | true =>
      simp only [d81986, d94475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81987 q = 1) (hb : d94476 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d81987, d94476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81987, d94476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d81988 q = 1) (hb : d94477 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d81988, d94477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81988, d94477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81989 q = 1) (hb : d94478 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d81989, d94478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81989, d94478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d81990 q = 1) (hb : d94479 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d81990, d94479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81990, d94479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d81991 q = 1) (hb : d94480 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d81991, d94480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d81991, d94480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19105 (p : Pattern) (ha : d81997 p = 1) (hb : d94486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81992 q = 1) (hb : d94481 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d81992, d94481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19104 q ha hb
    | true =>
      simp only [d81992, d94481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81993 q = 1) (hb : d94482 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d81993, d94482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81993, d94482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d81994 q = 1) (hb : d94483 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d81994, d94483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81994, d94483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81995 q = 1) (hb : d94484 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d81995, d94484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81995, d94484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d81996 q = 1) (hb : d94485 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d81996, d94485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81996, d94485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d81997 q = 1) (hb : d94486 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d81997, d94486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d81997, d94486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19106 (p : Pattern) (ha : d82003 p = 1) (hb : d94492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81998 q = 1) (hb : d94487 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d81998, d94487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19105 q ha hb
    | true =>
      simp only [d81998, d94487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81999 q = 1) (hb : d94488 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d81999, d94488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81999, d94488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82000 q = 1) (hb : d94489 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82000, d94489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82000, d94489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82001 q = 1) (hb : d94490 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82001, d94490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82001, d94490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82002 q = 1) (hb : d94491 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82002, d94491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82002, d94491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82003 q = 1) (hb : d94492 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82003, d94492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82003, d94492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19107 (p : Pattern) (ha : d82009 p = 1) (hb : d94498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82004 q = 1) (hb : d94493 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82004, d94493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19106 q ha hb
    | true =>
      simp only [d82004, d94493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82005 q = 1) (hb : d94494 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82005, d94494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82005, d94494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82006 q = 1) (hb : d94495 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82006, d94495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82006, d94495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82007 q = 1) (hb : d94496 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82007, d94496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82007, d94496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82008 q = 1) (hb : d94497 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82008, d94497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82008, d94497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82009 q = 1) (hb : d94498 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82009, d94498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82009, d94498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19108 (p : Pattern) (ha : d82015 p = 1) (hb : d94504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82010 q = 1) (hb : d94499 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82010, d94499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19107 q ha hb
    | true =>
      simp only [d82010, d94499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82011 q = 1) (hb : d94500 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82011, d94500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82011, d94500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82012 q = 1) (hb : d94501 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82012, d94501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82012, d94501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82013 q = 1) (hb : d94502 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82013, d94502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82013, d94502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82014 q = 1) (hb : d94503 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82014, d94503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82014, d94503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82015 q = 1) (hb : d94504 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82015, d94504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82015, d94504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19109 (p : Pattern) (ha : d82021 p = 1) (hb : d94510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82016 q = 1) (hb : d94505 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82016, d94505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19108 q ha hb
    | true =>
      simp only [d82016, d94505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82017 q = 1) (hb : d94506 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82017, d94506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82017, d94506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82018 q = 1) (hb : d94507 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82018, d94507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82018, d94507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82019 q = 1) (hb : d94508 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82019, d94508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82019, d94508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82020 q = 1) (hb : d94509 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82020, d94509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82020, d94509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82021 q = 1) (hb : d94510 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82021, d94510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82021, d94510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19110 (p : Pattern) (ha : d82027 p = 1) (hb : d94516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82022 q = 1) (hb : d94511 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82022, d94511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19109 q ha hb
    | true =>
      simp only [d82022, d94511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82023 q = 1) (hb : d94512 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82023, d94512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82023, d94512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82024 q = 1) (hb : d94513 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82024, d94513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82024, d94513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82025 q = 1) (hb : d94514 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82025, d94514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82025, d94514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82026 q = 1) (hb : d94515 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82026, d94515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82026, d94515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82027 q = 1) (hb : d94516 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82027, d94516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82027, d94516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19111 (p : Pattern) (ha : d94518 p = 1) (hb : d94751 p = 1) : d94751 p = 1 := by
  have h0 (q : Pattern) (ha : d94518 q = 1) (hb : d94751 q = 1) : d94751 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro19112 (p : Pattern) (ha : d8289 p = 1) (hb : d81539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8239 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18923 q ha hb
    | true =>
      simp only [d8239, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d8285 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8285, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8286 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8286, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8287 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8287, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8288 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8288, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8289 q = 1) (hb : d81539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19113 (p : Pattern) (ha : d8296 p = 1) (hb : d81546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8239 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18923 q ha hb
    | true =>
      simp only [d8239, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d8285 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8285, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8286 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8286, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8287 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8287, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8288 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8246 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18925 q ha hb
    | true =>
      simp only [d8246, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d8292 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8292, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8293 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8293, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8294 q = 1) (hb : d81544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8294, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8295 q = 1) (hb : d81545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8295, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8296 q = 1) (hb : d81546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8296, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19114 (p : Pattern) (ha : d81553 p = 1) (hb : d94521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18925 q ha hb
    | true =>
      simp only [d8246, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d8292 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8292, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8293 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8293, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8294 q = 1) (hb : d81551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8295 q = 1) (hb : d81552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81553 q = 1) (hb : d94521 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81553, d94521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81553, d94521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19115 (p : Pattern) (ha : d81572 p = 1) (hb : d94531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18929 q ha hb
    | true =>
      simp only [d8268, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d81568 q = 1) (hb : d94527 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81568, d94527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81568, d94527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81569 q = 1) (hb : d94528 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81569, d94528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81569, d94528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81570 q = 1) (hb : d94529 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81570, d94529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81570, d94529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81571 q = 1) (hb : d94530 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81571, d94530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81571, d94530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81572 q = 1) (hb : d94531 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81572, d94531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81572, d94531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19116 (p : Pattern) (ha : d81578 p = 1) (hb : d94537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d81547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19112 q ha hb
    | true =>
      simp only [d8297, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19113 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8298 q = 1) (hb : d81548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81549 q = 1) (hb : d94519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81549, d94519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81549, d94519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81550 q = 1) (hb : d94520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81550, d94520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81550, d94520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81554 q = 1) (hb : d94522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81554, d94522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81554, d94522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19114 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81555 q = 1) (hb : d94523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81555, d94523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81555, d94523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81556 q = 1) (hb : d94524 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81556, d94524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81556, d94524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81557 q = 1) (hb : d94525 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81557, d94525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81557, d94525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81558 q = 1) (hb : d94526 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81558, d94526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81558, d94526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81573 q = 1) (hb : d94532 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81573, d94532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81573, d94532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19115 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81574 q = 1) (hb : d94533 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81574, d94533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81574, d94533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81575 q = 1) (hb : d94534 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81575, d94534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81575, d94534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81576 q = 1) (hb : d94535 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81576, d94535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81576, d94535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81577 q = 1) (hb : d94536 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81577, d94536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81577, d94536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81578 q = 1) (hb : d94537 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81578, d94537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81578, d94537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19117 (p : Pattern) (ha : d81584 p = 1) (hb : d94543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81579 q = 1) (hb : d94538 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81579, d94538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81579, d94538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19116 q ha hb
  have h8 (q : Pattern) (ha : d81580 q = 1) (hb : d94539 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81580, d94539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81580, d94539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81581 q = 1) (hb : d94540 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81581, d94540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81581, d94540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81582 q = 1) (hb : d94541 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81582, d94541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81582, d94541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81583 q = 1) (hb : d94542 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81583, d94542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81583, d94542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d81584 q = 1) (hb : d94543 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81584, d94543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81584, d94543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19118 (p : Pattern) (ha : d8426 p = 1) (hb : d81603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8421 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18954 q ha hb
    | true =>
      simp only [d8421, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h5 (q : Pattern) (ha : d8422 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8422, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8423 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8423, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8424 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8424, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8425 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8425, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8426 q = 1) (hb : d81603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19119 (p : Pattern) (ha : d8435 p = 1) (hb : d81611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8421 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18954 q ha hb
    | true =>
      simp only [d8421, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d8422 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8422, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8423 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8423, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8424 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8424, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8425 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8430 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18956 q ha hb
    | true =>
      simp only [d8430, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h13 (q : Pattern) (ha : d8431 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8431, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8432 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8432, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8433 q = 1) (hb : d81609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8433, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8434 q = 1) (hb : d81610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8434, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8435 q = 1) (hb : d81611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8435, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19120 (p : Pattern) (ha : d81625 p = 1) (hb : d94546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8430 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18956 q ha hb
    | true =>
      simp only [d8430, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h3 (q : Pattern) (ha : d8431 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8431, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8432 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8432, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8433 q = 1) (hb : d81623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8434 q = 1) (hb : d81624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81625 q = 1) (hb : d94546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81625, d94546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81625, d94546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19121 (p : Pattern) (ha : d52393 p = 1) (hb : d94555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18978 q ha hb
    | true =>
      simp only [d8378, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52390 q = 1) (hb : d94552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52390, d94552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52390, d94552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52391 q = 1) (hb : d94553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52391, d94553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52391, d94553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52392 q = 1) (hb : d94554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52392, d94554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52392, d94554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52393 q = 1) (hb : d94555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52393, d94555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52393, d94555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro19122 (p : Pattern) (ha : d81649 p = 1) (hb : d94561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52399 q = 1) (hb : d94556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52399, d94556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19121 q ha hb
    | true =>
      simp only [d52399, d94556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d81645 q = 1) (hb : d94557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81645, d94557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81645, d94557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81646 q = 1) (hb : d94558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81646, d94558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81646, d94558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81647 q = 1) (hb : d94559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81647, d94559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81647, d94559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81648 q = 1) (hb : d94560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81648, d94560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81648, d94560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81649 q = 1) (hb : d94561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81649, d94561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81649, d94561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19123 (p : Pattern) (ha : d81655 p = 1) (hb : d94567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d81612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19118 q ha hb
    | true =>
      simp only [d8436, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19119 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8437 q = 1) (hb : d81620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81621 q = 1) (hb : d94544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81621, d94544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81621, d94544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81622 q = 1) (hb : d94545 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81622, d94545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81622, d94545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81626 q = 1) (hb : d94547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81626, d94547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81626, d94547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19120 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81627 q = 1) (hb : d94548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81627, d94548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81627, d94548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81628 q = 1) (hb : d94549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81628, d94549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81628, d94549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81629 q = 1) (hb : d94550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81629, d94550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81629, d94550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81630 q = 1) (hb : d94551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81630, d94551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81630, d94551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81650 q = 1) (hb : d94562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81650, d94562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81650, d94562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19122 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81651 q = 1) (hb : d94563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81651, d94563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81651, d94563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81652 q = 1) (hb : d94564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81652, d94564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81652, d94564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81653 q = 1) (hb : d94565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81653, d94565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81653, d94565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81654 q = 1) (hb : d94566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81654, d94566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81654, d94566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81655 q = 1) (hb : d94567 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81655, d94567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81655, d94567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19124 (p : Pattern) (ha : d81661 p = 1) (hb : d94573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81656 q = 1) (hb : d94568 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81656, d94568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81656, d94568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19123 q ha hb
  have h2 (q : Pattern) (ha : d81657 q = 1) (hb : d94569 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81657, d94569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81657, d94569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81658 q = 1) (hb : d94570 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81658, d94570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81658, d94570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81659 q = 1) (hb : d94571 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81659, d94571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81659, d94571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81660 q = 1) (hb : d94572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81660, d94572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81660, d94572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81661 q = 1) (hb : d94573 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81661, d94573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81661, d94573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19125 (p : Pattern) (ha : d8588 p = 1) (hb : d81681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8583 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18984 q ha hb
    | true =>
      simp only [d8583, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h5 (q : Pattern) (ha : d8584 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8584, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8585 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8585, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8586 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8586, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8587 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8587, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8588 q = 1) (hb : d81681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19126 (p : Pattern) (ha : d8597 p = 1) (hb : d81689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8583 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18984 q ha hb
    | true =>
      simp only [d8583, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d8584 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8584, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8585 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8585, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8586 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8586, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8587 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8592 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18986 q ha hb
    | true =>
      simp only [d8592, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h13 (q : Pattern) (ha : d8593 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8593, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8594 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8594, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8595 q = 1) (hb : d81687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8595, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8596 q = 1) (hb : d81688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8596, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8597 q = 1) (hb : d81689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8597, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19127 (p : Pattern) (ha : d81703 p = 1) (hb : d94577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8592 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18986 q ha hb
    | true =>
      simp only [d8592, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h3 (q : Pattern) (ha : d8593 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8593, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8594 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8594, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8595 q = 1) (hb : d81701 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8596 q = 1) (hb : d81702 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81703 q = 1) (hb : d94577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81703, d94577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81703, d94577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19128 (p : Pattern) (ha : d52630 p = 1) (hb : d94586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19008 q ha hb
    | true =>
      simp only [d8716, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52627 q = 1) (hb : d94583 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52627, d94583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52627, d94583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52628 q = 1) (hb : d94584 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52628, d94584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52628, d94584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52629 q = 1) (hb : d94585 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52629, d94585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52629, d94585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52630 q = 1) (hb : d94586 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52630, d94586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52630, d94586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro19129 (p : Pattern) (ha : d81727 p = 1) (hb : d94592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81722 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52636 q = 1) (hb : d94587 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52636, d94587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19128 q ha hb
    | true =>
      simp only [d52636, d94587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d81723 q = 1) (hb : d94588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81723, d94588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81723, d94588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81724 q = 1) (hb : d94589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81724, d94589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81724, d94589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81725 q = 1) (hb : d94590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81725, d94590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81725, d94590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81726 q = 1) (hb : d94591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81726, d94591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81726, d94591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81727 q = 1) (hb : d94592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81727, d94592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81727, d94592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19130 (p : Pattern) (ha : d81733 p = 1) (hb : d94598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d81690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19125 q ha hb
    | true =>
      simp only [d8598, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19126 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8599 q = 1) (hb : d81698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81699 q = 1) (hb : d94575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81699, d94575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81699, d94575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81700 q = 1) (hb : d94576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81700, d94576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81700, d94576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81704 q = 1) (hb : d94578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81704, d94578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81704, d94578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19127 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81705 q = 1) (hb : d94579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81705, d94579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81705, d94579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81706 q = 1) (hb : d94580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81706, d94580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81706, d94580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81707 q = 1) (hb : d94581 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81707, d94581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81707, d94581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81708 q = 1) (hb : d94582 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81708, d94582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81708, d94582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81728 q = 1) (hb : d94593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81728, d94593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81728, d94593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19129 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81729 q = 1) (hb : d94594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81729, d94594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81729, d94594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81730 q = 1) (hb : d94595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81730, d94595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81730, d94595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81731 q = 1) (hb : d94596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81731, d94596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81731, d94596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81732 q = 1) (hb : d94597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81732, d94597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81732, d94597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81733 q = 1) (hb : d94598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81733, d94598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81733, d94598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19131 (p : Pattern) (ha : d81739 p = 1) (hb : d94604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81734 q = 1) (hb : d94599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81734, d94599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81734, d94599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19130 q ha hb
  have h2 (q : Pattern) (ha : d81735 q = 1) (hb : d94600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81735, d94600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81735, d94600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81736 q = 1) (hb : d94601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81736, d94601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81736, d94601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81737 q = 1) (hb : d94602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81737, d94602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81737, d94602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81738 q = 1) (hb : d94603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81738, d94603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81738, d94603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81739 q = 1) (hb : d94604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81739, d94604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81739, d94604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19132 (p : Pattern) (ha : d8755 p = 1) (hb : d81760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8750 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19014 q ha hb
    | true =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h5 (q : Pattern) (ha : d8751 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8751, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8752 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8752, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8753 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8753, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8754 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8754, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8755 q = 1) (hb : d81760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19133 (p : Pattern) (ha : d8764 p = 1) (hb : d81768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8750 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19014 q ha hb
    | true =>
      simp only [d8750, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d8751 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8751, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8752 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8752, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8753 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8753, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8754 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8759 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19016 q ha hb
    | true =>
      simp only [d8759, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h13 (q : Pattern) (ha : d8760 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8760, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8761 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8761, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8762 q = 1) (hb : d81766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8762, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8763 q = 1) (hb : d81767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8763, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8764 q = 1) (hb : d81768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8764, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19134 (p : Pattern) (ha : d81782 p = 1) (hb : d94609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8759 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19016 q ha hb
    | true =>
      simp only [d8759, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h3 (q : Pattern) (ha : d8760 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8760, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8761 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8761, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8762 q = 1) (hb : d81780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8763 q = 1) (hb : d81781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81782 q = 1) (hb : d94609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81782, d94609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81782, d94609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19135 (p : Pattern) (ha : d52924 p = 1) (hb : d94618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19038 q ha hb
    | true =>
      simp only [d8883, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52921 q = 1) (hb : d94615 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52921, d94615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52921, d94615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52922 q = 1) (hb : d94616 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52922, d94616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52922, d94616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52923 q = 1) (hb : d94617 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52923, d94617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52923, d94617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52924 q = 1) (hb : d94618 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52924, d94618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52924, d94618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro19136 (p : Pattern) (ha : d81806 p = 1) (hb : d94624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d94619 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d94619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19135 q ha hb
    | true =>
      simp only [d52930, d94619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d81802 q = 1) (hb : d94620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81802, d94620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81802, d94620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81803 q = 1) (hb : d94621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81803, d94621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81803, d94621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81804 q = 1) (hb : d94622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81804, d94622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81804, d94622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81805 q = 1) (hb : d94623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81805, d94623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81805, d94623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81806 q = 1) (hb : d94624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81806, d94624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81806, d94624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19137 (p : Pattern) (ha : d81812 p = 1) (hb : d94630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d81769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19132 q ha hb
    | true =>
      simp only [d8765, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19133 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8766 q = 1) (hb : d81777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81778 q = 1) (hb : d94607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81778, d94607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81778, d94607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81779 q = 1) (hb : d94608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81779, d94608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81779, d94608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81783 q = 1) (hb : d94610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81783, d94610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81783, d94610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19134 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81784 q = 1) (hb : d94611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81784, d94611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81784, d94611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81785 q = 1) (hb : d94612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81785, d94612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81785, d94612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81786 q = 1) (hb : d94613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81786, d94613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81786, d94613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81787 q = 1) (hb : d94614 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81787, d94614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81787, d94614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81807 q = 1) (hb : d94625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81807, d94625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81807, d94625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19136 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81808 q = 1) (hb : d94626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81808, d94626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81808, d94626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81809 q = 1) (hb : d94627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81809, d94627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81809, d94627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81810 q = 1) (hb : d94628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81810, d94628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81810, d94628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81811 q = 1) (hb : d94629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81811, d94629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81811, d94629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81812 q = 1) (hb : d94630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81812, d94630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81812, d94630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19138 (p : Pattern) (ha : d81818 p = 1) (hb : d94636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81813 q = 1) (hb : d94631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81813, d94631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81813, d94631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19137 q ha hb
  have h2 (q : Pattern) (ha : d81814 q = 1) (hb : d94632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81814, d94632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81814, d94632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81815 q = 1) (hb : d94633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81815, d94633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81815, d94633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81816 q = 1) (hb : d94634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81816, d94634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81816, d94634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81817 q = 1) (hb : d94635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81817, d94635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81817, d94635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81818 q = 1) (hb : d94636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81818, d94636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81818, d94636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19139 (p : Pattern) (ha : d8923 p = 1) (hb : d81840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8918 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19044 q ha hb
    | true =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h5 (q : Pattern) (ha : d8919 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8919, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8920 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8920, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8921 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8921, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8922 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8922, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8923 q = 1) (hb : d81840 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19140 (p : Pattern) (ha : d8932 p = 1) (hb : d81848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8918 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19044 q ha hb
    | true =>
      simp only [d8918, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d8919 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8919, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8920 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8920, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8921 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8921, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8922 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8927 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19046 q ha hb
    | true =>
      simp only [d8927, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h13 (q : Pattern) (ha : d8928 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8928, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8929 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8929, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8930 q = 1) (hb : d81846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8930, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8931 q = 1) (hb : d81847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8931, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8932 q = 1) (hb : d81848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8932, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19141 (p : Pattern) (ha : d81862 p = 1) (hb : d94642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8927 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19046 q ha hb
    | true =>
      simp only [d8927, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h3 (q : Pattern) (ha : d8928 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8928, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8929 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8929, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8930 q = 1) (hb : d81860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8931 q = 1) (hb : d81861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81862 q = 1) (hb : d94642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81862, d94642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81862, d94642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19142 (p : Pattern) (ha : d53239 p = 1) (hb : d94651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19068 q ha hb
    | true =>
      simp only [d9051, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53236 q = 1) (hb : d94648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53236, d94648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53236, d94648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53237 q = 1) (hb : d94649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53237, d94649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53237, d94649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53238 q = 1) (hb : d94650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53238, d94650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53238, d94650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53239 q = 1) (hb : d94651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53239, d94651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53239, d94651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro19143 (p : Pattern) (ha : d81886 p = 1) (hb : d94657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d94652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d94652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19142 q ha hb
    | true =>
      simp only [d53245, d94652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d81882 q = 1) (hb : d94653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81882, d94653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81882, d94653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81883 q = 1) (hb : d94654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81883, d94654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81883, d94654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81884 q = 1) (hb : d94655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81884, d94655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81884, d94655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81885 q = 1) (hb : d94656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81885, d94656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81885, d94656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81886 q = 1) (hb : d94657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81886, d94657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81886, d94657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19144 (p : Pattern) (ha : d81892 p = 1) (hb : d94663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d81849 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19139 q ha hb
    | true =>
      simp only [d8933, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19140 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8934 q = 1) (hb : d81857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81858 q = 1) (hb : d94640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81858, d94640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81858, d94640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81859 q = 1) (hb : d94641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81859, d94641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81859, d94641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81863 q = 1) (hb : d94643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81863, d94643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81863, d94643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19141 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81864 q = 1) (hb : d94644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81864, d94644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81864, d94644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81865 q = 1) (hb : d94645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81865, d94645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81865, d94645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81866 q = 1) (hb : d94646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81866, d94646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81866, d94646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81867 q = 1) (hb : d94647 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81867, d94647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81867, d94647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81887 q = 1) (hb : d94658 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81887, d94658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81887, d94658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19143 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81888 q = 1) (hb : d94659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81888, d94659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81888, d94659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81889 q = 1) (hb : d94660 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81889, d94660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81889, d94660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81890 q = 1) (hb : d94661 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81890, d94661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81890, d94661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81891 q = 1) (hb : d94662 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81891, d94662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81891, d94662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81892 q = 1) (hb : d94663 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81892, d94663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81892, d94663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19145 (p : Pattern) (ha : d81898 p = 1) (hb : d94669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81893 q = 1) (hb : d94664 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81893, d94664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81893, d94664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19144 q ha hb
  have h2 (q : Pattern) (ha : d81894 q = 1) (hb : d94665 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81894, d94665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81894, d94665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81895 q = 1) (hb : d94666 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81895, d94666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81895, d94666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81896 q = 1) (hb : d94667 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81896, d94667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81896, d94667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81897 q = 1) (hb : d94668 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81897, d94668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81897, d94668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81898 q = 1) (hb : d94669 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81898, d94669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81898, d94669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19146 (p : Pattern) (ha : d9092 p = 1) (hb : d81921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9087 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19074 q ha hb
    | true =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h5 (q : Pattern) (ha : d9088 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9088, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9089 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9089, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9090 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9090, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9091 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9091, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9092 q = 1) (hb : d81921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19147 (p : Pattern) (ha : d9101 p = 1) (hb : d81929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9087 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19074 q ha hb
    | true =>
      simp only [d9087, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d9088 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9088, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9089 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9089, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9090 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9090, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9091 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9096 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19076 q ha hb
    | true =>
      simp only [d9096, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h13 (q : Pattern) (ha : d9097 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9097, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9098 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9098, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9099 q = 1) (hb : d81927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9099, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9100 q = 1) (hb : d81928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9100, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9101 q = 1) (hb : d81929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9101, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19148 (p : Pattern) (ha : d81943 p = 1) (hb : d94676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9096 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19076 q ha hb
    | true =>
      simp only [d9096, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h3 (q : Pattern) (ha : d9097 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9097, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9098 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9098, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9099 q = 1) (hb : d81941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9100 q = 1) (hb : d81942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81943 q = 1) (hb : d94676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81943, d94676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81943, d94676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19149 (p : Pattern) (ha : d53556 p = 1) (hb : d94685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19098 q ha hb
    | true =>
      simp only [d9220, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53553 q = 1) (hb : d94682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53553, d94682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53553, d94682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53554 q = 1) (hb : d94683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53554, d94683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53554, d94683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53555 q = 1) (hb : d94684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53555, d94684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53555, d94684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53556 q = 1) (hb : d94685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53556, d94685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53556, d94685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro19150 (p : Pattern) (ha : d81967 p = 1) (hb : d94691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81962 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d94686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d94686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19149 q ha hb
    | true =>
      simp only [d53562, d94686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d81963 q = 1) (hb : d94687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81963, d94687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81963, d94687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81964 q = 1) (hb : d94688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81964, d94688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81964, d94688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81965 q = 1) (hb : d94689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81965, d94689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81965, d94689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81966 q = 1) (hb : d94690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81966, d94690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81966, d94690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81967 q = 1) (hb : d94691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81967, d94691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81967, d94691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19151 (p : Pattern) (ha : d81973 p = 1) (hb : d94697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d81930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19146 q ha hb
    | true =>
      simp only [d9102, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19147 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81937 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9103 q = 1) (hb : d81938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81939 q = 1) (hb : d94674 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81939, d94674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81939, d94674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81940 q = 1) (hb : d94675 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81940, d94675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81940, d94675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81944 q = 1) (hb : d94677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81944, d94677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81944, d94677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19148 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81945 q = 1) (hb : d94678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81945, d94678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81945, d94678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81946 q = 1) (hb : d94679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81946, d94679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81946, d94679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81947 q = 1) (hb : d94680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81947, d94680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81947, d94680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81948 q = 1) (hb : d94681 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81948, d94681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81948, d94681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81968 q = 1) (hb : d94692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81968, d94692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81968, d94692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19150 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81969 q = 1) (hb : d94693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81969, d94693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81969, d94693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81970 q = 1) (hb : d94694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81970, d94694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81970, d94694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81971 q = 1) (hb : d94695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81971, d94695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81971, d94695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81972 q = 1) (hb : d94696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81972, d94696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81972, d94696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81973 q = 1) (hb : d94697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81973, d94697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81973, d94697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19152 (p : Pattern) (ha : d81979 p = 1) (hb : d94703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81974 q = 1) (hb : d94698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81974, d94698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81974, d94698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19151 q ha hb
  have h2 (q : Pattern) (ha : d81975 q = 1) (hb : d94699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81975, d94699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81975, d94699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81976 q = 1) (hb : d94700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81976, d94700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81976, d94700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81977 q = 1) (hb : d94701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81977, d94701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81977, d94701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81978 q = 1) (hb : d94702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81978, d94702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81978, d94702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81979 q = 1) (hb : d94703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81979, d94703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81979, d94703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19153 (p : Pattern) (ha : d81985 p = 1) (hb : d94709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d81662 q = 1) (hb : d94574 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81662, d94574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19117 q ha hb
    | true =>
      simp only [d81662, d94574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19124 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d81740 q = 1) (hb : d94605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81740, d94605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81740, d94605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19131 q ha hb
  have h3 (q : Pattern) (ha : d81741 q = 1) (hb : d94606 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81741, d94606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d81741, d94606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81819 q = 1) (hb : d94637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81819, d94637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81819, d94637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19138 q ha hb
  have h5 (q : Pattern) (ha : d81820 q = 1) (hb : d94638 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81820, d94638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81820, d94638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81821 q = 1) (hb : d94639 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81821, d94639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81821, d94639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81899 q = 1) (hb : d94670 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81899, d94670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81899, d94670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19145 q ha hb
  have h8 (q : Pattern) (ha : d81900 q = 1) (hb : d94671 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81900, d94671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81900, d94671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81901 q = 1) (hb : d94672 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81901, d94672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81901, d94672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81902 q = 1) (hb : d94673 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d81902, d94673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81902, d94673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81980 q = 1) (hb : d94704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81980, d94704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81980, d94704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19152 q ha hb
  have h12 (q : Pattern) (ha : d81981 q = 1) (hb : d94705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81981, d94705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81981, d94705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81982 q = 1) (hb : d94706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81982, d94706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81982, d94706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d81983 q = 1) (hb : d94707 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d81983, d94707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81983, d94707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81984 q = 1) (hb : d94708 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d81984, d94708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81984, d94708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d81985 q = 1) (hb : d94709 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d81985, d94709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81985, d94709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro19154 (p : Pattern) (ha : d81991 p = 1) (hb : d94715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81986 q = 1) (hb : d94710 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d81986, d94710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19153 q ha hb
    | true =>
      simp only [d81986, d94710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81987 q = 1) (hb : d94711 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d81987, d94711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81987, d94711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d81988 q = 1) (hb : d94712 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d81988, d94712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81988, d94712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81989 q = 1) (hb : d94713 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d81989, d94713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81989, d94713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d81990 q = 1) (hb : d94714 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d81990, d94714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81990, d94714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d81991 q = 1) (hb : d94715 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d81991, d94715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d81991, d94715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19155 (p : Pattern) (ha : d81997 p = 1) (hb : d94721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81992 q = 1) (hb : d94716 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d81992, d94716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19154 q ha hb
    | true =>
      simp only [d81992, d94716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81993 q = 1) (hb : d94717 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d81993, d94717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81993, d94717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d81994 q = 1) (hb : d94718 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d81994, d94718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81994, d94718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81995 q = 1) (hb : d94719 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d81995, d94719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81995, d94719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d81996 q = 1) (hb : d94720 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d81996, d94720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81996, d94720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d81997 q = 1) (hb : d94721 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d81997, d94721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d81997, d94721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19156 (p : Pattern) (ha : d82003 p = 1) (hb : d94727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81998 q = 1) (hb : d94722 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d81998, d94722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19155 q ha hb
    | true =>
      simp only [d81998, d94722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81999 q = 1) (hb : d94723 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d81999, d94723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81999, d94723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82000 q = 1) (hb : d94724 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82000, d94724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82000, d94724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82001 q = 1) (hb : d94725 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82001, d94725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82001, d94725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82002 q = 1) (hb : d94726 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82002, d94726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82002, d94726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82003 q = 1) (hb : d94727 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82003, d94727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82003, d94727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19157 (p : Pattern) (ha : d82009 p = 1) (hb : d94733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82004 q = 1) (hb : d94728 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82004, d94728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19156 q ha hb
    | true =>
      simp only [d82004, d94728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82005 q = 1) (hb : d94729 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82005, d94729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82005, d94729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82006 q = 1) (hb : d94730 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82006, d94730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82006, d94730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82007 q = 1) (hb : d94731 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82007, d94731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82007, d94731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82008 q = 1) (hb : d94732 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82008, d94732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82008, d94732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82009 q = 1) (hb : d94733 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82009, d94733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82009, d94733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19158 (p : Pattern) (ha : d82015 p = 1) (hb : d94739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82010 q = 1) (hb : d94734 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82010, d94734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19157 q ha hb
    | true =>
      simp only [d82010, d94734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82011 q = 1) (hb : d94735 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82011, d94735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82011, d94735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82012 q = 1) (hb : d94736 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82012, d94736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82012, d94736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82013 q = 1) (hb : d94737 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82013, d94737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82013, d94737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82014 q = 1) (hb : d94738 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82014, d94738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82014, d94738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82015 q = 1) (hb : d94739 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82015, d94739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82015, d94739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19159 (p : Pattern) (ha : d82021 p = 1) (hb : d94745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82016 q = 1) (hb : d94740 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82016, d94740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19158 q ha hb
    | true =>
      simp only [d82016, d94740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82017 q = 1) (hb : d94741 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82017, d94741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82017, d94741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82018 q = 1) (hb : d94742 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82018, d94742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82018, d94742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82019 q = 1) (hb : d94743 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82019, d94743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82019, d94743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82020 q = 1) (hb : d94744 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82020, d94744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82020, d94744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82021 q = 1) (hb : d94745 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82021, d94745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82021, d94745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19160 (p : Pattern) (ha : d82027 p = 1) (hb : d94751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82022 q = 1) (hb : d94746 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82022, d94746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19159 q ha hb
    | true =>
      simp only [d82022, d94746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82023 q = 1) (hb : d94747 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82023, d94747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82023, d94747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82024 q = 1) (hb : d94748 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82024, d94748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82024, d94748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82025 q = 1) (hb : d94749 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82025, d94749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82025, d94749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82026 q = 1) (hb : d94750 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82026, d94750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82026, d94750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82027 q = 1) (hb : d94751 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82027, d94751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82027, d94751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro19161 (p : Pattern) (ha : d8289 p = 1) (hb : d82032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6746 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8285 q = 1) (hb : d82028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8285, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8286 q = 1) (hb : d82029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8286, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8287 q = 1) (hb : d82030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8287, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8288 q = 1) (hb : d82031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8288, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8289 q = 1) (hb : d82032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d82032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d82032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19162 (p : Pattern) (ha : d8296 p = 1) (hb : d82037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6746 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8239 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8285 q = 1) (hb : d82028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8285, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8286 q = 1) (hb : d82029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8286, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8287 q = 1) (hb : d82030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8287, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8288 q = 1) (hb : d82031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8246 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8292 q = 1) (hb : d82033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8292, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8293 q = 1) (hb : d82034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8293, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8294 q = 1) (hb : d82035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d82035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8294, d82035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8295 q = 1) (hb : d82036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d82036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8295, d82036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8296 q = 1) (hb : d82037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d82037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8296, d82037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19163 (p : Pattern) (ha : d82044 p = 1) (hb : d94521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8246 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8292 q = 1) (hb : d82033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8292, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8293 q = 1) (hb : d82034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8293, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8294 q = 1) (hb : d82042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d82042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d82042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8295 q = 1) (hb : d82043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d82043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d82043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82044 q = 1) (hb : d94521 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82044, d94521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82044, d94521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19164 (p : Pattern) (ha : d82054 p = 1) (hb : d94531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8268 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82050 q = 1) (hb : d94527 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82050, d94527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82050, d94527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82051 q = 1) (hb : d94528 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82051, d94528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82051, d94528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82052 q = 1) (hb : d94529 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82052, d94529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82052, d94529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82053 q = 1) (hb : d94530 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82053, d94530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82053, d94530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82054 q = 1) (hb : d94531 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82054, d94531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82054, d94531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19165 (p : Pattern) (ha : d82060 p = 1) (hb : d94537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d82038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d82038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19161 q ha hb
    | true =>
      simp only [d8297, d82038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19162 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8298 q = 1) (hb : d82039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d82039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, d82039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82040 q = 1) (hb : d94519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82040, d94519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82040, d94519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82041 q = 1) (hb : d94520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82041, d94520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82041, d94520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82045 q = 1) (hb : d94522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82045, d94522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82045, d94522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19163 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82046 q = 1) (hb : d94523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82046, d94523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82046, d94523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82047 q = 1) (hb : d94524 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82047, d94524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82047, d94524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82048 q = 1) (hb : d94525 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82048, d94525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82048, d94525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82049 q = 1) (hb : d94526 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82049, d94526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82049, d94526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82055 q = 1) (hb : d94532 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82055, d94532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82055, d94532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19164 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82056 q = 1) (hb : d94533 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82056, d94533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82056, d94533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82057 q = 1) (hb : d94534 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82057, d94534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82057, d94534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82058 q = 1) (hb : d94535 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82058, d94535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82058, d94535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82059 q = 1) (hb : d94536 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82059, d94536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82059, d94536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82060 q = 1) (hb : d94537 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82060, d94537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82060, d94537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19166 (p : Pattern) (ha : d82066 p = 1) (hb : d94543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82061 q = 1) (hb : d94538 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82061, d94538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82061, d94538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19165 q ha hb
  have h8 (q : Pattern) (ha : d82062 q = 1) (hb : d94539 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82062, d94539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82062, d94539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82063 q = 1) (hb : d94540 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82063, d94540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82063, d94540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82064 q = 1) (hb : d94541 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82064, d94541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82064, d94541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82065 q = 1) (hb : d94542 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82065, d94542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82065, d94542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82066 q = 1) (hb : d94543 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82066, d94543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82066, d94543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19167 (p : Pattern) (ha : d8426 p = 1) (hb : d82071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6810 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8421 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8422 q = 1) (hb : d82067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8422, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8423 q = 1) (hb : d82068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8423, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8424 q = 1) (hb : d82069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8424, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8425 q = 1) (hb : d82070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8425, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8426 q = 1) (hb : d82071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d82071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d82071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19168 (p : Pattern) (ha : d8435 p = 1) (hb : d82076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6810 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8421 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8422 q = 1) (hb : d82067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8422, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8423 q = 1) (hb : d82068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8423, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8424 q = 1) (hb : d82069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8424, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8425 q = 1) (hb : d82070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d614 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6818 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8430 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8431 q = 1) (hb : d82072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8431, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8432 q = 1) (hb : d82073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8432, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8433 q = 1) (hb : d82074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d82074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8433, d82074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8434 q = 1) (hb : d82075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d82075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8434, d82075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8435 q = 1) (hb : d82076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d82076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8435, d82076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19169 (p : Pattern) (ha : d82083 p = 1) (hb : d94546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8430 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8431 q = 1) (hb : d82072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8431, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8432 q = 1) (hb : d82073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8432, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8433 q = 1) (hb : d82081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d82081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d82081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8434 q = 1) (hb : d82082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d82082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d82082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82083 q = 1) (hb : d94546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82083, d94546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82083, d94546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19170 (p : Pattern) (ha : d82093 p = 1) (hb : d94561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94556 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82089 q = 1) (hb : d94557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82089, d94557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82089, d94557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82090 q = 1) (hb : d94558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82090, d94558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82090, d94558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82091 q = 1) (hb : d94559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82091, d94559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82091, d94559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82092 q = 1) (hb : d94560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82092, d94560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82092, d94560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82093 q = 1) (hb : d94561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82093, d94561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82093, d94561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19171 (p : Pattern) (ha : d82099 p = 1) (hb : d94567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d82077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19167 q ha hb
    | true =>
      simp only [d8436, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19168 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6831 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8437 q = 1) (hb : d82078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82079 q = 1) (hb : d94544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82079, d94544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82079, d94544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82080 q = 1) (hb : d94545 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82080, d94545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82080, d94545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82084 q = 1) (hb : d94547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82084, d94547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82084, d94547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19169 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82085 q = 1) (hb : d94548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82085, d94548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82085, d94548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82086 q = 1) (hb : d94549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82086, d94549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82086, d94549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82087 q = 1) (hb : d94550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82087, d94550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82087, d94550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82088 q = 1) (hb : d94551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82088, d94551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82088, d94551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82094 q = 1) (hb : d94562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82094, d94562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82094, d94562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19170 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82095 q = 1) (hb : d94563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82095, d94563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82095, d94563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82096 q = 1) (hb : d94564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82096, d94564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82096, d94564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82097 q = 1) (hb : d94565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82097, d94565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82097, d94565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82098 q = 1) (hb : d94566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82098, d94566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82098, d94566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82099 q = 1) (hb : d94567 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82099, d94567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82099, d94567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19172 (p : Pattern) (ha : d82105 p = 1) (hb : d94573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82100 q = 1) (hb : d94568 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82100, d94568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82100, d94568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19171 q ha hb
  have h2 (q : Pattern) (ha : d82101 q = 1) (hb : d94569 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82101, d94569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82101, d94569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82102 q = 1) (hb : d94570 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82102, d94570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82102, d94570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82103 q = 1) (hb : d94571 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82103, d94571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82103, d94571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82104 q = 1) (hb : d94572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82104, d94572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82104, d94572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82105 q = 1) (hb : d94573 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82105, d94573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82105, d94573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19173 (p : Pattern) (ha : d8588 p = 1) (hb : d82111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8583 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8584 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8584, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8585 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8585, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8586 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8586, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8587 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8587, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8588 q = 1) (hb : d82111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19174 (p : Pattern) (ha : d8597 p = 1) (hb : d82116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8584 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8584, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8585 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8585, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8586 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8586, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8587 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8592 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8593 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8593, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8594 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8594, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8595 q = 1) (hb : d82114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8595, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8596 q = 1) (hb : d82115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8596, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8597 q = 1) (hb : d82116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8597, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19175 (p : Pattern) (ha : d82123 p = 1) (hb : d94577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8592 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8593 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8593, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8594 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8594, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8595 q = 1) (hb : d82121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8596 q = 1) (hb : d82122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82123 q = 1) (hb : d94577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82123, d94577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82123, d94577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19176 (p : Pattern) (ha : d82133 p = 1) (hb : d94592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82129 q = 1) (hb : d94588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82129, d94588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82129, d94588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82130 q = 1) (hb : d94589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82130, d94589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82130, d94589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82131 q = 1) (hb : d94590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82131, d94590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82131, d94590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82132 q = 1) (hb : d94591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82132, d94591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82132, d94591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82133 q = 1) (hb : d94592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82133, d94592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82133, d94592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19177 (p : Pattern) (ha : d82139 p = 1) (hb : d94598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d82117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19173 q ha hb
    | true =>
      simp only [d8598, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19174 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8599 q = 1) (hb : d82118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82119 q = 1) (hb : d94575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82119, d94575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82119, d94575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82120 q = 1) (hb : d94576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82120, d94576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82120, d94576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82124 q = 1) (hb : d94578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82124, d94578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82124, d94578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19175 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82125 q = 1) (hb : d94579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82125, d94579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82125, d94579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82126 q = 1) (hb : d94580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82126, d94580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82126, d94580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82127 q = 1) (hb : d94581 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82127, d94581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82127, d94581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82128 q = 1) (hb : d94582 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82128, d94582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82128, d94582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82134 q = 1) (hb : d94593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82134, d94593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82134, d94593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19176 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82135 q = 1) (hb : d94594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82135, d94594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82135, d94594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82136 q = 1) (hb : d94595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82136, d94595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82136, d94595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82137 q = 1) (hb : d94596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82137, d94596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82137, d94596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82138 q = 1) (hb : d94597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82138, d94597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82138, d94597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82139 q = 1) (hb : d94598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82139, d94598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82139, d94598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19178 (p : Pattern) (ha : d82145 p = 1) (hb : d94604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82140 q = 1) (hb : d94599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82140, d94599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82140, d94599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19177 q ha hb
  have h2 (q : Pattern) (ha : d82141 q = 1) (hb : d94600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82141, d94600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82141, d94600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82142 q = 1) (hb : d94601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82142, d94601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82142, d94601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82143 q = 1) (hb : d94602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82143, d94602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82143, d94602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82144 q = 1) (hb : d94603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82144, d94603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82144, d94603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82145 q = 1) (hb : d94604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82145, d94604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82145, d94604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19179 (p : Pattern) (ha : d8755 p = 1) (hb : d82152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8751 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8751, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8752 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8752, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8753 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8753, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8754 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8754, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8755 q = 1) (hb : d82152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19180 (p : Pattern) (ha : d8764 p = 1) (hb : d82157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8750 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8751 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8751, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8752 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8752, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8753 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8753, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8754 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8759 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8760 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8760, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8761 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8761, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8762 q = 1) (hb : d82155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8762, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8763 q = 1) (hb : d82156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8763, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8764 q = 1) (hb : d82157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8764, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19181 (p : Pattern) (ha : d82164 p = 1) (hb : d94609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8759 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8760 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8760, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8761 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8761, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8762 q = 1) (hb : d82162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8763 q = 1) (hb : d82163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82164 q = 1) (hb : d94609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82164, d94609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82164, d94609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19182 (p : Pattern) (ha : d82174 p = 1) (hb : d94624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82170 q = 1) (hb : d94620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82170, d94620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82170, d94620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6380 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82171 q = 1) (hb : d94621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82171, d94621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82171, d94621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82172 q = 1) (hb : d94622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82172, d94622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82172, d94622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82173 q = 1) (hb : d94623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82173, d94623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82173, d94623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82174 q = 1) (hb : d94624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82174, d94624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82174, d94624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19183 (p : Pattern) (ha : d82180 p = 1) (hb : d94630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d82158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19179 q ha hb
    | true =>
      simp only [d8765, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19180 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8766 q = 1) (hb : d82159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82160 q = 1) (hb : d94607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82160, d94607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82160, d94607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82161 q = 1) (hb : d94608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82161, d94608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82161, d94608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82165 q = 1) (hb : d94610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82165, d94610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82165, d94610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19181 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82166 q = 1) (hb : d94611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82166, d94611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82166, d94611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82167 q = 1) (hb : d94612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82167, d94612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82167, d94612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82168 q = 1) (hb : d94613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82168, d94613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82168, d94613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82169 q = 1) (hb : d94614 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82169, d94614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82169, d94614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82175 q = 1) (hb : d94625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82175, d94625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82175, d94625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19182 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82176 q = 1) (hb : d94626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82176, d94626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82176, d94626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82177 q = 1) (hb : d94627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82177, d94627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82177, d94627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82178 q = 1) (hb : d94628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82178, d94628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82178, d94628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82179 q = 1) (hb : d94629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82179, d94629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82179, d94629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82180 q = 1) (hb : d94630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82180, d94630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82180, d94630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19184 (p : Pattern) (ha : d82186 p = 1) (hb : d94636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82181 q = 1) (hb : d94631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82181, d94631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82181, d94631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19183 q ha hb
  have h2 (q : Pattern) (ha : d82182 q = 1) (hb : d94632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82182, d94632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82182, d94632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82183 q = 1) (hb : d94633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82183, d94633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82183, d94633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82184 q = 1) (hb : d94634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82184, d94634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82184, d94634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82185 q = 1) (hb : d94635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82185, d94635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82185, d94635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82186 q = 1) (hb : d94636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82186, d94636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82186, d94636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19185 (p : Pattern) (ha : d8923 p = 1) (hb : d82194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8918 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8919 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8919, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8920 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8920, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8921 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8921, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8922 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8922, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8923 q = 1) (hb : d82194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19186 (p : Pattern) (ha : d8932 p = 1) (hb : d82199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8918 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8919 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8919, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8920 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8920, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8921 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8921, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8922 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8927 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8928 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8928, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8929 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8929, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8930 q = 1) (hb : d82197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8930, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8931 q = 1) (hb : d82198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8931, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8932 q = 1) (hb : d82199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8932, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19187 (p : Pattern) (ha : d82206 p = 1) (hb : d94642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8928 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8928, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8929 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8929, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8930 q = 1) (hb : d82204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8931 q = 1) (hb : d82205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82206 q = 1) (hb : d94642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82206, d94642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82206, d94642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19188 (p : Pattern) (ha : d82216 p = 1) (hb : d94657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82212 q = 1) (hb : d94653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82212, d94653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82212, d94653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82213 q = 1) (hb : d94654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82213, d94654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82213, d94654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82214 q = 1) (hb : d94655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82214, d94655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82214, d94655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82215 q = 1) (hb : d94656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82215, d94656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82215, d94656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82216 q = 1) (hb : d94657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82216, d94657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82216, d94657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19189 (p : Pattern) (ha : d82222 p = 1) (hb : d94663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d82200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19185 q ha hb
    | true =>
      simp only [d8933, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19186 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7068 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8934 q = 1) (hb : d82201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82202 q = 1) (hb : d94640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82202, d94640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82202, d94640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82203 q = 1) (hb : d94641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82203, d94641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82203, d94641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82207 q = 1) (hb : d94643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82207, d94643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82207, d94643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19187 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82208 q = 1) (hb : d94644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82208, d94644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82208, d94644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82209 q = 1) (hb : d94645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82209, d94645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82209, d94645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82210 q = 1) (hb : d94646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82210, d94646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82210, d94646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82211 q = 1) (hb : d94647 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82211, d94647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82211, d94647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82217 q = 1) (hb : d94658 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82217, d94658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82217, d94658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19188 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82218 q = 1) (hb : d94659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82218, d94659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82218, d94659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82219 q = 1) (hb : d94660 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82219, d94660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82219, d94660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82220 q = 1) (hb : d94661 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82220, d94661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82220, d94661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82221 q = 1) (hb : d94662 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82221, d94662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82221, d94662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82222 q = 1) (hb : d94663 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82222, d94663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82222, d94663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19190 (p : Pattern) (ha : d82228 p = 1) (hb : d94669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82223 q = 1) (hb : d94664 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82223, d94664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82223, d94664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19189 q ha hb
  have h2 (q : Pattern) (ha : d82224 q = 1) (hb : d94665 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82224, d94665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82224, d94665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82225 q = 1) (hb : d94666 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82225, d94666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82225, d94666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82226 q = 1) (hb : d94667 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82226, d94667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82226, d94667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82227 q = 1) (hb : d94668 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82227, d94668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82227, d94668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82228 q = 1) (hb : d94669 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82228, d94669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82228, d94669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19191 (p : Pattern) (ha : d9092 p = 1) (hb : d82237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9087 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9088 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9088, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9089 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9089, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9090 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9090, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9091 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9091, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9092 q = 1) (hb : d82237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19192 (p : Pattern) (ha : d9101 p = 1) (hb : d82242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9087 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9088 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9088, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9089 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9089, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9090 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9090, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9091 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9096 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9097 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9097, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9098 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9098, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9099 q = 1) (hb : d82240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9099, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9100 q = 1) (hb : d82241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9100, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9101 q = 1) (hb : d82242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9101, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro19193 (p : Pattern) (ha : d82249 p = 1) (hb : d94676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9097 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9097, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9098 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9098, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9099 q = 1) (hb : d82247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9100 q = 1) (hb : d82248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82249 q = 1) (hb : d94676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82249, d94676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82249, d94676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro19194 (p : Pattern) (ha : d82259 p = 1) (hb : d94691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82255 q = 1) (hb : d94687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, d94687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82255, d94687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82256 q = 1) (hb : d94688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, d94688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82256, d94688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82257 q = 1) (hb : d94689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, d94689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82257, d94689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82258 q = 1) (hb : d94690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, d94690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82258, d94690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82259 q = 1) (hb : d94691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, d94691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82259, d94691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19195 (p : Pattern) (ha : d82265 p = 1) (hb : d94697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d82243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19191 q ha hb
    | true =>
      simp only [d9102, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19192 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9103 q = 1) (hb : d82244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82245 q = 1) (hb : d94674 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, d94674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82245, d94674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82246 q = 1) (hb : d94675 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, d94675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82246, d94675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82250 q = 1) (hb : d94677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, d94677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82250, d94677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19193 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82251 q = 1) (hb : d94678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, d94678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82251, d94678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82252 q = 1) (hb : d94679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, d94679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82252, d94679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82253 q = 1) (hb : d94680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, d94680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82253, d94680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82254 q = 1) (hb : d94681 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, d94681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82254, d94681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82260 q = 1) (hb : d94692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, d94692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82260, d94692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19194 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82261 q = 1) (hb : d94693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, d94693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82261, d94693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82262 q = 1) (hb : d94694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, d94694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82262, d94694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82263 q = 1) (hb : d94695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, d94695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82263, d94695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82264 q = 1) (hb : d94696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, d94696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82264, d94696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82265 q = 1) (hb : d94697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, d94697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82265, d94697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19196 (p : Pattern) (ha : d82271 p = 1) (hb : d94703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82266 q = 1) (hb : d94698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, d94698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82266, d94698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19195 q ha hb
  have h2 (q : Pattern) (ha : d82267 q = 1) (hb : d94699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, d94699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82267, d94699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82268 q = 1) (hb : d94700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, d94700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82268, d94700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82269 q = 1) (hb : d94701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, d94701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82269, d94701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82270 q = 1) (hb : d94702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, d94702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82270, d94702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82271 q = 1) (hb : d94703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, d94703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82271, d94703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19197 (p : Pattern) (ha : d82277 p = 1) (hb : d94709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d82106 q = 1) (hb : d94574 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, d94574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19166 q ha hb
    | true =>
      simp only [d82106, d94574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19172 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82146 q = 1) (hb : d94605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, d94605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82146, d94605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19178 q ha hb
  have h3 (q : Pattern) (ha : d82147 q = 1) (hb : d94606 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, d94606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, d94606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82187 q = 1) (hb : d94637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, d94637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82187, d94637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19184 q ha hb
  have h5 (q : Pattern) (ha : d82188 q = 1) (hb : d94638 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, d94638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82188, d94638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82189 q = 1) (hb : d94639 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, d94639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, d94639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82229 q = 1) (hb : d94670 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, d94670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82229, d94670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19190 q ha hb
  have h8 (q : Pattern) (ha : d82230 q = 1) (hb : d94671 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, d94671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82230, d94671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82231 q = 1) (hb : d94672 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, d94672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82231, d94672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82232 q = 1) (hb : d94673 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, d94673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, d94673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82272 q = 1) (hb : d94704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, d94704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82272, d94704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19196 q ha hb
  have h12 (q : Pattern) (ha : d82273 q = 1) (hb : d94705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, d94705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82273, d94705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82274 q = 1) (hb : d94706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, d94706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82274, d94706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82275 q = 1) (hb : d94707 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, d94707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82275, d94707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82276 q = 1) (hb : d94708 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, d94708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, d94708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82277 q = 1) (hb : d94709 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, d94709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, d94709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro19198 (p : Pattern) (ha : d82283 p = 1) (hb : d94715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82278 q = 1) (hb : d94710 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, d94710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19197 q ha hb
    | true =>
      simp only [d82278, d94710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82279 q = 1) (hb : d94711 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, d94711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, d94711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82280 q = 1) (hb : d94712 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, d94712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, d94712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82281 q = 1) (hb : d94713 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, d94713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, d94713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82282 q = 1) (hb : d94714 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, d94714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, d94714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82283 q = 1) (hb : d94715 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, d94715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, d94715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19199 (p : Pattern) (ha : d82289 p = 1) (hb : d94721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82284 q = 1) (hb : d94716 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, d94716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19198 q ha hb
    | true =>
      simp only [d82284, d94716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82285 q = 1) (hb : d94717 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, d94717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, d94717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82286 q = 1) (hb : d94718 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, d94718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, d94718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82287 q = 1) (hb : d94719 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, d94719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, d94719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82288 q = 1) (hb : d94720 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, d94720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, d94720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82289 q = 1) (hb : d94721 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, d94721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, d94721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19200 (p : Pattern) (ha : d82295 p = 1) (hb : d94727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82290 q = 1) (hb : d94722 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, d94722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19199 q ha hb
    | true =>
      simp only [d82290, d94722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82291 q = 1) (hb : d94723 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, d94723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, d94723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82292 q = 1) (hb : d94724 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, d94724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, d94724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82293 q = 1) (hb : d94725 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, d94725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, d94725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82294 q = 1) (hb : d94726 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, d94726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, d94726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82295 q = 1) (hb : d94727 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, d94727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, d94727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19201 (p : Pattern) (ha : d82301 p = 1) (hb : d94733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82296 q = 1) (hb : d94728 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, d94728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19200 q ha hb
    | true =>
      simp only [d82296, d94728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82297 q = 1) (hb : d94729 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, d94729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, d94729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82298 q = 1) (hb : d94730 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, d94730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, d94730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82299 q = 1) (hb : d94731 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, d94731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, d94731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82300 q = 1) (hb : d94732 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, d94732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, d94732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82301 q = 1) (hb : d94733 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, d94733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, d94733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19202 (p : Pattern) (ha : d82307 p = 1) (hb : d94739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82302 q = 1) (hb : d94734 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, d94734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19201 q ha hb
    | true =>
      simp only [d82302, d94734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82303 q = 1) (hb : d94735 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, d94735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, d94735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82304 q = 1) (hb : d94736 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d94736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82304, d94736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82305 q = 1) (hb : d94737 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, d94737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82305, d94737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82306 q = 1) (hb : d94738 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, d94738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82306, d94738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82307 q = 1) (hb : d94739 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, d94739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82307, d94739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19203 (p : Pattern) (ha : d82313 p = 1) (hb : d94745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d94740 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, d94740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19202 q ha hb
    | true =>
      simp only [d82308, d94740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d94741 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, d94741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, d94741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d94742 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, d94742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, d94742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d94743 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, d94743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, d94743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d94744 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, d94744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, d94744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d94745 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, d94745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, d94745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19204 (p : Pattern) (ha : d82319 p = 1) (hb : d94751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d94746 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, d94746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19203 q ha hb
    | true =>
      simp only [d82314, d94746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d94747 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, d94747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, d94747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d94748 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, d94748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, d94748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d94749 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, d94749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, d94749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d94750 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, d94750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, d94750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d94751 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, d94751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, d94751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19205 (p : Pattern) (ha : d6739 p = 1) (hb : d115574 p = 1) : d115576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d94753 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d94753 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d115574 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6738 q = 1) (hb : d115574 q = 1) : d115575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6738, d115575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6738, d115575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6739 q = 1) (hb : d115574 q = 1) : d115576 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6739, d115576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6739, d115576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19206 (p : Pattern) (ha : d8238 p = 1) (hb : d115574 p = 1) : d115582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d115574 q = 1) : d115581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8238 q = 1) (hb : d115574 q = 1) : d115582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d115582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d115582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro19207 (p : Pattern) (ha : d94191 p = 1) (hb : d115574 p = 1) : d115588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d115574 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d115574 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8239 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
    | true =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94187 q = 1) (hb : d115574 q = 1) : d115584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94187, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d115574 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94188 q = 1) (hb : d115574 q = 1) : d115585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94189 q = 1) (hb : d115574 q = 1) : d115586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94189, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94190 q = 1) (hb : d115574 q = 1) : d115587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94190, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94191 q = 1) (hb : d115574 q = 1) : d115588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d115588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94191, d115588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19208 (p : Pattern) (ha : d8245 p = 1) (hb : d115574 p = 1) : d115589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d115574 q = 1) : d115581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8245 q = 1) (hb : d115574 q = 1) : d115589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d115589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8245, d115589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro19209 (p : Pattern) (ha : d94196 p = 1) (hb : d115574 p = 1) : d115595 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d115574 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d115574 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8239 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
    | true =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94187 q = 1) (hb : d115574 q = 1) : d115584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94187, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d115574 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94188 q = 1) (hb : d115574 q = 1) : d115585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94189 q = 1) (hb : d115574 q = 1) : d115586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94189, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94190 q = 1) (hb : d115574 q = 1) : d115587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94190, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d115574 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d115574 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d115574 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8246 q = 1) (hb : d115574 q = 1) : d115590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19208 q ha hb
    | true =>
      simp only [d8246, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94192 q = 1) (hb : d115574 q = 1) : d115591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94192, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d115574 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d94193 q = 1) (hb : d115574 q = 1) : d115592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94193, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94194 q = 1) (hb : d115574 q = 1) : d115593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d115593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94194, d115593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94195 q = 1) (hb : d115574 q = 1) : d115594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d115594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94195, d115594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d94196 q = 1) (hb : d115574 q = 1) : d115595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d115595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94196, d115595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro19210 (p : Pattern) (ha : d94203 p = 1) (hb : d115574 p = 1) : d115602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d115574 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d115574 q = 1) : d115590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19208 q ha hb
    | true =>
      simp only [d8246, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94192 q = 1) (hb : d115574 q = 1) : d115591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94192, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d115574 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94193 q = 1) (hb : d115574 q = 1) : d115592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94193, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94201 q = 1) (hb : d115574 q = 1) : d115600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d115600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94201, d115600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94202 q = 1) (hb : d115574 q = 1) : d115601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d115601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94202, d115601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94203 q = 1) (hb : d115574 q = 1) : d115602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d115602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94203, d115602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19211 (p : Pattern) (ha : d6772 p = 1) (hb : d115574 p = 1) : d115609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d94753 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d94753 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d115574 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d115574 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6771 q = 1) (hb : d115574 q = 1) : d115608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6771, d115608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6771, d115608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6772 q = 1) (hb : d115574 q = 1) : d115609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6772, d115609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6772, d115609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro19212 (p : Pattern) (ha : d8267 p = 1) (hb : d115574 p = 1) : d115615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d115574 q = 1) : d115610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19211 q ha hb
    | true =>
      simp only [d6773, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d115574 q = 1) : d115611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d115574 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8264 q = 1) (hb : d115574 q = 1) : d115612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d115612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8264, d115612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8265 q = 1) (hb : d115574 q = 1) : d115613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d115613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8265, d115613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8266 q = 1) (hb : d115574 q = 1) : d115614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d115614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8266, d115614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8267 q = 1) (hb : d115574 q = 1) : d115615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d115615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8267, d115615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro19213 (p : Pattern) (ha : d94213 p = 1) (hb : d115574 p = 1) : d115621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d115574 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d115574 q = 1) : d115616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d115616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19212 q ha hb
    | true =>
      simp only [d8268, d115616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94209 q = 1) (hb : d115574 q = 1) : d115617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d115617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94209, d115617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d115574 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94210 q = 1) (hb : d115574 q = 1) : d115618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d115618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94210, d115618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94211 q = 1) (hb : d115574 q = 1) : d115619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d115619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94211, d115619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94212 q = 1) (hb : d115574 q = 1) : d115620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d115620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94212, d115620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94213 q = 1) (hb : d115574 q = 1) : d115621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d115621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94213, d115621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19214 (p : Pattern) (ha : d94219 p = 1) (hb : d115574 p = 1) : d115627 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d115574 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94197 q = 1) (hb : d115574 q = 1) : d115596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d115596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19207 q ha hb
    | true =>
      simp only [d94197, d115596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19209 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d115574 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94198 q = 1) (hb : d115574 q = 1) : d115597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d115597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94198, d115597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94199 q = 1) (hb : d115574 q = 1) : d115598 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d115598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94199, d115598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94200 q = 1) (hb : d115574 q = 1) : d115599 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d115599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94200, d115599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94204 q = 1) (hb : d115574 q = 1) : d115603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d115603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94204, d115603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19210 q ha hb
  have h8 (q : Pattern) (ha : d94205 q = 1) (hb : d115574 q = 1) : d115604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d115604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94205, d115604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d94206 q = 1) (hb : d115574 q = 1) : d115605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d115605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94206, d115605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d94207 q = 1) (hb : d115574 q = 1) : d115606 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d115606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94207, d115606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94208 q = 1) (hb : d115574 q = 1) : d115607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d115607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94208, d115607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94214 q = 1) (hb : d115574 q = 1) : d115622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d115622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94214, d115622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19213 q ha hb
  have h13 (q : Pattern) (ha : d94215 q = 1) (hb : d115574 q = 1) : d115623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d115623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94215, d115623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d94216 q = 1) (hb : d115574 q = 1) : d115624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d115624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94216, d115624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d94217 q = 1) (hb : d115574 q = 1) : d115625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d115625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94217, d115625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d94218 q = 1) (hb : d115574 q = 1) : d115626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d115626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94218, d115626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94219 q = 1) (hb : d115574 q = 1) : d115627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d115627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94219, d115627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro19215 (p : Pattern) (ha : d8289 p = 1) (hb : d115574 p = 1) : d115637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
    | true =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d115574 q = 1) : d115633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d115574 q = 1) : d115634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d115574 q = 1) : d115635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d115574 q = 1) : d115636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8289 q = 1) (hb : d115574 q = 1) : d115637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro19216 (p : Pattern) (ha : d8296 p = 1) (hb : d115574 p = 1) : d115644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
    | true =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d115574 q = 1) : d115633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d115574 q = 1) : d115634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d115574 q = 1) : d115635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d115574 q = 1) : d115636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d115574 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8246 q = 1) (hb : d115574 q = 1) : d115590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19208 q ha hb
    | true =>
      simp only [d8246, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8292 q = 1) (hb : d115574 q = 1) : d115640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8293 q = 1) (hb : d115574 q = 1) : d115641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8293, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8294 q = 1) (hb : d115574 q = 1) : d115642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8295 q = 1) (hb : d115574 q = 1) : d115643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8296 q = 1) (hb : d115574 q = 1) : d115644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8296, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro19217 (p : Pattern) (ha : d8363 p = 1) (hb : d115574 p = 1) : d115701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
    | true =>
      simp only [d8239, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d115574 q = 1) : d115633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d115574 q = 1) : d115634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d115574 q = 1) : d115635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d115574 q = 1) : d115636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d115574 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8363 q = 1) (hb : d115574 q = 1) : d115701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d115701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8363, d115701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19218 (p : Pattern) (ha : d8301 p = 1) (hb : d115574 p = 1) : d115649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d115574 q = 1) : d115648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8301 q = 1) (hb : d115574 q = 1) : d115649 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d115649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d115649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro19219 (p : Pattern) (ha : d8308 p = 1) (hb : d115574 p = 1) : d115656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d115574 q = 1) : d115654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d115574 q = 1) : d115655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8308 q = 1) (hb : d115574 q = 1) : d115656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d115656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d115656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro19220 (p : Pattern) (ha : d8313 p = 1) (hb : d115574 p = 1) : d115662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d94753 q = 1) : d12313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d12313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d325, d12313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d94753 q = 1) : d12314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d12314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d12314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d12315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d12315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d115574 q = 1) : d115660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145 q = 1) (hb : d94753 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146 q = 1) (hb : d94753 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d475 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d475, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d8312 q = 1) (hb : d115574 q = 1) : d115661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8312, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8313 q = 1) (hb : d115574 q = 1) : d115662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8313, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro19221 (p : Pattern) (ha : d8319 p = 1) (hb : d115574 p = 1) : d115668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19220 q ha hb
    | true =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d115574 q = 1) : d115665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d115574 q = 1) : d115666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d115574 q = 1) : d115667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8319 q = 1) (hb : d115574 q = 1) : d115668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d115668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d115668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19222 (p : Pattern) (ha : d8334 p = 1) (hb : d115574 p = 1) : d115674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d115574 q = 1) : d115671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d115574 q = 1) : d115672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d115574 q = 1) : d115673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d115574 q = 1) : d115674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d115674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d115674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19223 (p : Pattern) (ha : d94229 p = 1) (hb : d115574 p = 1) : d115680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d115574 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d115574 q = 1) : d115650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19218 q ha hb
    | true =>
      simp only [d8302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d115574 q = 1) : d115651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d115574 q = 1) : d115652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d115574 q = 1) : d115653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d115574 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d115574 q = 1) : d115657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19219 q ha hb
    | true =>
      simp only [d8309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d115574 q = 1) : d115658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d115574 q = 1) : d115659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d115574 q = 1) : d115669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19221 q ha hb
    | true =>
      simp only [d8320, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
  have h11 (q : Pattern) (ha : d94225 q = 1) (hb : d115574 q = 1) : d115670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94225, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d115574 q = 1) : d115675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19222 q ha hb
    | true =>
      simp only [d8335, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d115574 q = 1) : d115676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94226 q = 1) (hb : d115574 q = 1) : d115677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94227 q = 1) (hb : d115574 q = 1) : d115678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94227, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94228 q = 1) (hb : d115574 q = 1) : d115679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94228, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94229 q = 1) (hb : d115574 q = 1) : d115680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d115680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d115680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro19224 (p : Pattern) (ha : d8341 p = 1) (hb : d115574 p = 1) : d115681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d115574 q = 1) : d115648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8341 q = 1) (hb : d115574 q = 1) : d115681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d115681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8341, d115681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro19225 (p : Pattern) (ha : d8346 p = 1) (hb : d115574 p = 1) : d115686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d115574 q = 1) : d115654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d115574 q = 1) : d115655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8346 q = 1) (hb : d115574 q = 1) : d115686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d115686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8346, d115686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro19226 (p : Pattern) (ha : d8350 p = 1) (hb : d115574 p = 1) : d115690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19220 q ha hb
    | true =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d115574 q = 1) : d115665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d115574 q = 1) : d115666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d115574 q = 1) : d115667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8350 q = 1) (hb : d115574 q = 1) : d115690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d115690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8350, d115690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19227 (p : Pattern) (ha : d8355 p = 1) (hb : d115574 p = 1) : d115693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19205 q ha hb
    | true =>
      simp only [d6740, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d115574 q = 1) : d115671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d115574 q = 1) : d115672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d115574 q = 1) : d115673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d115574 q = 1) : d115693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d115693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d115693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19228 (p : Pattern) (ha : d94234 p = 1) (hb : d115574 p = 1) : d115699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d115574 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d115574 q = 1) : d115650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19218 q ha hb
    | true =>
      simp only [d8302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d115574 q = 1) : d115651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d115574 q = 1) : d115652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d115574 q = 1) : d115653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d115574 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d115574 q = 1) : d115657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19219 q ha hb
    | true =>
      simp only [d8309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d115574 q = 1) : d115658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d115574 q = 1) : d115659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d115574 q = 1) : d115669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19221 q ha hb
    | true =>
      simp only [d8320, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19206 q ha hb
  have h11 (q : Pattern) (ha : d94225 q = 1) (hb : d115574 q = 1) : d115670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94225, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d115574 q = 1) : d115675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19222 q ha hb
    | true =>
      simp only [d8335, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d115574 q = 1) : d115676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94226 q = 1) (hb : d115574 q = 1) : d115677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94227 q = 1) (hb : d115574 q = 1) : d115678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94227, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94228 q = 1) (hb : d115574 q = 1) : d115679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94228, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d115574 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8342 q = 1) (hb : d115574 q = 1) : d115682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d115682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19224 q ha hb
    | true =>
      simp only [d8342, d115682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8343 q = 1) (hb : d115574 q = 1) : d115683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d115683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d115683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8344 q = 1) (hb : d115574 q = 1) : d115684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d115684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8344, d115684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8345 q = 1) (hb : d115574 q = 1) : d115685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d115685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d115685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d115574 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8347 q = 1) (hb : d115574 q = 1) : d115687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d115687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19225 q ha hb
    | true =>
      simp only [d8347, d115687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8348 q = 1) (hb : d115574 q = 1) : d115688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d115688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d115688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8349 q = 1) (hb : d115574 q = 1) : d115689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d115689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8349, d115689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8351 q = 1) (hb : d115574 q = 1) : d115691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19226 q ha hb
    | true =>
      simp only [d8351, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19208 q ha hb
  have h27 (q : Pattern) (ha : d94230 q = 1) (hb : d115574 q = 1) : d115692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94230, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d8356 q = 1) (hb : d115574 q = 1) : d115694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19227 q ha hb
    | true =>
      simp only [d8356, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8357 q = 1) (hb : d115574 q = 1) : d115695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8357, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d94231 q = 1) (hb : d115574 q = 1) : d115696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94231, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d94232 q = 1) (hb : d115574 q = 1) : d115697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d115697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d94232, d115697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d94233 q = 1) (hb : d115574 q = 1) : d115698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d115698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94233, d115698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d94234 q = 1) (hb : d115574 q = 1) : d115699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d115699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94234, d115699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro19229 (p : Pattern) (ha : d94241 p = 1) (hb : d115574 p = 1) : d115708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d115574 q = 1) : d115691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19226 q ha hb
    | true =>
      simp only [d8351, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19208 q ha hb
  have h2 (q : Pattern) (ha : d94230 q = 1) (hb : d115574 q = 1) : d115692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94230, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8356 q = 1) (hb : d115574 q = 1) : d115694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19227 q ha hb
    | true =>
      simp only [d8356, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8357 q = 1) (hb : d115574 q = 1) : d115695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8357, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d115574 q = 1) : d115696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d115574 q = 1) : d115706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d115706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d115706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d115574 q = 1) : d115707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d115707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d115707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d115574 q = 1) : d115708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d115708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d115708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19230 (p : Pattern) (ha : d8377 p = 1) (hb : d115574 p = 1) : d115716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d94753 q = 1) : d12387 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d12387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d418, d12387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d94753 q = 1) : d12388 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d12388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d12388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d12389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d12389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6843 q = 1) (hb : d115574 q = 1) : d115714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d232 q = 1) (hb : d94753 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233 q = 1) (hb : d94753 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d673 q = 1) (hb : d115574 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d673, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d8376 q = 1) (hb : d115574 q = 1) : d115715 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8376, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8377 q = 1) (hb : d115574 q = 1) : d115716 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8377, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro19231 (p : Pattern) (ha : d8383 p = 1) (hb : d115574 p = 1) : d115722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d115574 q = 1) : d115717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19230 q ha hb
    | true =>
      simp only [d8378, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d115574 q = 1) : d115718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6773 q = 1) (hb : d115574 q = 1) : d115610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19211 q ha hb
    | true =>
      simp only [d6773, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6774 q = 1) (hb : d115574 q = 1) : d115611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8380 q = 1) (hb : d115574 q = 1) : d115719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d115719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8380, d115719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8381 q = 1) (hb : d115574 q = 1) : d115720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d115720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8381, d115720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8382 q = 1) (hb : d115574 q = 1) : d115721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d115721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8382, d115721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8383 q = 1) (hb : d115574 q = 1) : d115722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d115722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8383, d115722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19232 (p : Pattern) (ha : d8398 p = 1) (hb : d115574 p = 1) : d115728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d115574 q = 1) : d115610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19211 q ha hb
    | true =>
      simp only [d6773, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d115574 q = 1) : d115611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d115574 q = 1) : d115725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d115725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d115725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d115574 q = 1) : d115726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d115726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d115726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d115574 q = 1) : d115727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d115727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d115727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d115574 q = 1) : d115728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d115728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d115728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19233 (p : Pattern) (ha : d94251 p = 1) (hb : d115574 p = 1) : d115734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d115574 q = 1) : d115723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d115723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19231 q ha hb
    | true =>
      simp only [d8384, d115723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19212 q ha hb
  have h2 (q : Pattern) (ha : d94247 q = 1) (hb : d115574 q = 1) : d115724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d115724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94247, d115724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8399 q = 1) (hb : d115574 q = 1) : d115729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d115729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19232 q ha hb
    | true =>
      simp only [d8399, d115729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8400 q = 1) (hb : d115574 q = 1) : d115730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d115730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8400, d115730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d115574 q = 1) : d115731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d115731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d115731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d115574 q = 1) : d115732 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d115732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d115732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d115574 q = 1) : d115733 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d115733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d115733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d115574 q = 1) : d115734 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d115734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d115734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19234 (p : Pattern) (ha : d94257 p = 1) (hb : d115574 p = 1) : d115740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d115574 q = 1) : d115638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d115638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d115638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19215 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d115574 q = 1) : d115639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d115639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d115639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d115574 q = 1) : d115645 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19215 q ha hb
    | true =>
      simp only [d8297, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19216 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d115574 q = 1) : d115646 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d115574 q = 1) : d115647 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d115647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d115647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94235 q = 1) (hb : d115574 q = 1) : d115700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d115700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19223 q ha hb
    | true =>
      simp only [d94235, d115700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19228 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d115574 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8364 q = 1) (hb : d115574 q = 1) : d115702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d115702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19217 q ha hb
    | true =>
      simp only [d8364, d115702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94236 q = 1) (hb : d115574 q = 1) : d115703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d115703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d115703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94237 q = 1) (hb : d115574 q = 1) : d115704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d115704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94237, d115704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d94238 q = 1) (hb : d115574 q = 1) : d115705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d115705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94238, d115705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94242 q = 1) (hb : d115574 q = 1) : d115709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d115709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94242, d115709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19229 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d115574 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d94243 q = 1) (hb : d115574 q = 1) : d115710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d115710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94243, d115710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94244 q = 1) (hb : d115574 q = 1) : d115711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d115711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94244, d115711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94245 q = 1) (hb : d115574 q = 1) : d115712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d115712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94245, d115712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d94246 q = 1) (hb : d115574 q = 1) : d115713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d115713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94246, d115713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94252 q = 1) (hb : d115574 q = 1) : d115735 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d115735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94252, d115735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19233 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d115574 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d94253 q = 1) (hb : d115574 q = 1) : d115736 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d115736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94253, d115736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d94254 q = 1) (hb : d115574 q = 1) : d115737 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d115737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94254, d115737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94255 q = 1) (hb : d115574 q = 1) : d115738 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d115738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94255, d115738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94256 q = 1) (hb : d115574 q = 1) : d115739 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d115739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94256, d115739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d94257 q = 1) (hb : d115574 q = 1) : d115740 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d115740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94257, d115740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro19235 (p : Pattern) (ha : d94263 p = 1) (hb : d115574 p = 1) : d115746 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d115574 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94220 q = 1) (hb : d115574 q = 1) : d115628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d115628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94220, d115628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19214 q ha hb
  have h3 (q : Pattern) (ha : d94221 q = 1) (hb : d115574 q = 1) : d115629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d115629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94221, d115629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94222 q = 1) (hb : d115574 q = 1) : d115630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d115630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94222, d115630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94223 q = 1) (hb : d115574 q = 1) : d115631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d115631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94223, d115631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94224 q = 1) (hb : d115574 q = 1) : d115632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d115632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94224, d115632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94258 q = 1) (hb : d115574 q = 1) : d115741 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d115741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94258, d115741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19234 q ha hb
  have h8 (q : Pattern) (ha : d94259 q = 1) (hb : d115574 q = 1) : d115742 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d115742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94259, d115742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94260 q = 1) (hb : d115574 q = 1) : d115743 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d115743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94260, d115743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94261 q = 1) (hb : d115574 q = 1) : d115744 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d115744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94261, d115744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94262 q = 1) (hb : d115574 q = 1) : d115745 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d115745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94262, d115745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94263 q = 1) (hb : d115574 q = 1) : d115746 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d115746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94263, d115746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro19236 (p : Pattern) (ha : d481 p = 1) (hb : d115574 p = 1) : d12442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d94753 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d94753 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d480 q = 1) (hb : d115574 q = 1) : d12441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d480, d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d481 q = 1) (hb : d115574 q = 1) : d12442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d481, d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro19237 (p : Pattern) (ha : d491 p = 1) (hb : d115574 p = 1) : d12452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d115574 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19236 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d115574 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d115574 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d115574 q = 1) : d12451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d115574 q = 1) : d12452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19238 (p : Pattern) (ha : d501 p = 1) (hb : d115574 p = 1) : d12462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d115574 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19236 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d115574 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d115574 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d115574 q = 1) : d12451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d115574 q = 1) : d12462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19239 (p : Pattern) (ha : d644 p = 1) (hb : d115574 p = 1) : d12580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d115574 q = 1) : d12569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19237 q ha hb
    | true =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d115574 q = 1) : d12570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d115574 q = 1) : d12571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d115574 q = 1) : d12572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d115574 q = 1) : d12573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d115574 q = 1) : d12575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19238 q ha hb
    | true =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d115574 q = 1) : d12576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d115574 q = 1) : d12577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d115574 q = 1) : d12578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d115574 q = 1) : d12579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d115574 q = 1) : d12580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19240 (p : Pattern) (ha : d653 p = 1) (hb : d115574 p = 1) : d12589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d115574 q = 1) : d12575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19238 q ha hb
    | true =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d115574 q = 1) : d12576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d115574 q = 1) : d12577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d115574 q = 1) : d12578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d115574 q = 1) : d12579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d115574 q = 1) : d12589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19241 (p : Pattern) (ha : d683 p = 1) (hb : d115574 p = 1) : d12622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d94753 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d94753 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d115574 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d682 q = 1) (hb : d115574 q = 1) : d12621 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d682, d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d683 q = 1) (hb : d115574 q = 1) : d12622 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d683, d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro19242 (p : Pattern) (ha : d730 p = 1) (hb : d115574 p = 1) : d12668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d115574 q = 1) : d12623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19241 q ha hb
    | true =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d115574 q = 1) : d12624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d115574 q = 1) : d12665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d115574 q = 1) : d12666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d115574 q = 1) : d12667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d115574 q = 1) : d12668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro19243 (p : Pattern) (ha : d736 p = 1) (hb : d115574 p = 1) : d12674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d115574 q = 1) : d12669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19242 q ha hb
    | true =>
      simp only [d731, d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d115574 q = 1) : d12670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d115574 q = 1) : d12671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d115574 q = 1) : d12672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d115574 q = 1) : d12673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d115574 q = 1) : d12674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19244 (p : Pattern) (ha : d8420 p = 1) (hb : d115574 p = 1) : d115750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19220 q ha hb
    | true =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d115574 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19236 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d115574 q = 1) : d115749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8420 q = 1) (hb : d115574 q = 1) : d115750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro19245 (p : Pattern) (ha : d8426 p = 1) (hb : d115574 p = 1) : d115756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d115574 q = 1) : d115751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19244 q ha hb
    | true =>
      simp only [d8421, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19237 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d115574 q = 1) : d115752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d115574 q = 1) : d115753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d115574 q = 1) : d115754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d115574 q = 1) : d115755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8426 q = 1) (hb : d115574 q = 1) : d115756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro19246 (p : Pattern) (ha : d8429 p = 1) (hb : d115574 p = 1) : d115759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19220 q ha hb
    | true =>
      simp only [d8314, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d115574 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19236 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d115574 q = 1) : d115749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8429 q = 1) (hb : d115574 q = 1) : d115759 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8429, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro19247 (p : Pattern) (ha : d8435 p = 1) (hb : d115574 p = 1) : d115765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d115574 q = 1) : d115751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19244 q ha hb
    | true =>
      simp only [d8421, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19237 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d115574 q = 1) : d115752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d115574 q = 1) : d115753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d115574 q = 1) : d115754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d115574 q = 1) : d115755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8430 q = 1) (hb : d115574 q = 1) : d115760 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d115760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19246 q ha hb
    | true =>
      simp only [d8430, d115760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19238 q ha hb
  have h7 (q : Pattern) (ha : d8431 q = 1) (hb : d115574 q = 1) : d115761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8432 q = 1) (hb : d115574 q = 1) : d115762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8432, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8433 q = 1) (hb : d115574 q = 1) : d115763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8434 q = 1) (hb : d115574 q = 1) : d115764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8435 q = 1) (hb : d115574 q = 1) : d115765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8435, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro19248 (p : Pattern) (ha : d6799 p = 1) (hb : d115574 p = 1) : d115662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d94753 q = 1) : d12313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d12313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d325, d12313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d94753 q = 1) : d12314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d12314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d12314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d12315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d12315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d115574 q = 1) : d115660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4822 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6798 q = 1) (hb : d115574 q = 1) : d115661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6798, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6799 q = 1) (hb : d115574 q = 1) : d115662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6799, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro19249 (p : Pattern) (ha : d8463 p = 1) (hb : d115574 p = 1) : d115750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19248 q ha hb
    | true =>
      simp only [d6800, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d115574 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19236 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d115574 q = 1) : d115749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8463 q = 1) (hb : d115574 q = 1) : d115750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
