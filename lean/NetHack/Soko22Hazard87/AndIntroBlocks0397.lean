import NetHack.Soko22Hazard87.AndIntroBlocks0396
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro99250 (p : Pattern) (ha : d262648 p = 1) (hb : d312674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262514 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98958 q ha hb
    | true =>
      simp only [d262514, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98959 q ha hb
  have h3 (q : Pattern) (ha : d262621 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262621, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262625 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262625, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262646 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262646, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262646, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262647 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262647, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262647, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262648 q = 1) (hb : d312674 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262648, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262648, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99251 (p : Pattern) (ha : d262733 p = 1) (hb : d312685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262722 q = 1) (hb : d312680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262722, d312680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98997 q ha hb
    | true =>
      simp only [d262722, d312680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99000 q ha hb
  have h3 (q : Pattern) (ha : d262723 q = 1) (hb : d312681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262723, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262723, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262730 q = 1) (hb : d312682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262730, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262730, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262731 q = 1) (hb : d312683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262731, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262731, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262732 q = 1) (hb : d312684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262732, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262732, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262733 q = 1) (hb : d312685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262733, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262733, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99252 (p : Pattern) (ha : d262746 p = 1) (hb : d312691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262522 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262629 q = 1) (hb : d311306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262629, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99248 q ha hb
    | true =>
      simp only [d262629, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99249 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262643 q = 1) (hb : d311307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262643, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262643, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262644 q = 1) (hb : d312672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262644, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262644, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262645 q = 1) (hb : d312673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262645, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262645, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262649 q = 1) (hb : d312675 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262649, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262649, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99250 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262652 q = 1) (hb : d312676 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262652, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262652, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262653 q = 1) (hb : d312677 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262653, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262653, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262654 q = 1) (hb : d312678 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262654, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262654, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262655 q = 1) (hb : d312679 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262655, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262655, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262734 q = 1) (hb : d312686 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262734, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262734, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99251 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262741 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262742 q = 1) (hb : d312687 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262742, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262742, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262743 q = 1) (hb : d312688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262743, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262743, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262744 q = 1) (hb : d312689 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262744, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262744, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262745 q = 1) (hb : d312690 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262745, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262745, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262746 q = 1) (hb : d312691 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262746, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262746, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99253 (p : Pattern) (ha : d262752 p = 1) (hb : d312697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262747 q = 1) (hb : d312692 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262747, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262747, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99252 q ha hb
  have h2 (q : Pattern) (ha : d262748 q = 1) (hb : d312693 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262748, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262748, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262749 q = 1) (hb : d312694 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262749, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262749, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262750 q = 1) (hb : d312695 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262750, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262750, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262751 q = 1) (hb : d312696 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262751, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262751, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262752 q = 1) (hb : d312697 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262752, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262752, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99254 (p : Pattern) (ha : d262965 p = 1) (hb : d311633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262846 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99015 q ha hb
    | true =>
      simp only [d262846, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99016 q ha hb
  have h5 (q : Pattern) (ha : d262946 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262946, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262962 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262962, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262963 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262963, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262964 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262964, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262965 q = 1) (hb : d311633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262965, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262965, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99255 (p : Pattern) (ha : d262986 p = 1) (hb : d311643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262846 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99015 q ha hb
    | true =>
      simp only [d262846, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99016 q ha hb
  have h4 (q : Pattern) (ha : d262946 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262946, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262962 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262962, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262963 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262963, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262964 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262964, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262976 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262856 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99018 q ha hb
    | true =>
      simp only [d262856, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99019 q ha hb
  have h13 (q : Pattern) (ha : d262979 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262979, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262983 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262983, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262984 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262984, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262984, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262985 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262985, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262985, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262986 q = 1) (hb : d311643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262986, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262986, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99256 (p : Pattern) (ha : d263006 p = 1) (hb : d312702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262856 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99018 q ha hb
    | true =>
      simp only [d262856, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99019 q ha hb
  have h3 (q : Pattern) (ha : d262979 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262979, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262983 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262983, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263004 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263004, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263004, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263005 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263005, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263005, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263006 q = 1) (hb : d312702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263006, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263006, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99257 (p : Pattern) (ha : d263127 p = 1) (hb : d312713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263107 q = 1) (hb : d312708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263107, d312708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99059 q ha hb
    | true =>
      simp only [d263107, d312708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99064 q ha hb
  have h3 (q : Pattern) (ha : d263108 q = 1) (hb : d312709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263108, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263108, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263124 q = 1) (hb : d312710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263124, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263124, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263125 q = 1) (hb : d312711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263125, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263125, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263126 q = 1) (hb : d312712 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263126, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263126, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263127 q = 1) (hb : d312713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263127, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263127, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99258 (p : Pattern) (ha : d263140 p = 1) (hb : d312719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262987 q = 1) (hb : d311644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262987, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99254 q ha hb
    | true =>
      simp only [d262987, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99255 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263001 q = 1) (hb : d311645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263001, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263001, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263002 q = 1) (hb : d312700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263002, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263002, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263003 q = 1) (hb : d312701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263003, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263003, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263007 q = 1) (hb : d312703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263007, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263007, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99256 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263010 q = 1) (hb : d312704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263010, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263010, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263011 q = 1) (hb : d312705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263011, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263011, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263012 q = 1) (hb : d312706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263012, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263012, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263013 q = 1) (hb : d312707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263013, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263013, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263128 q = 1) (hb : d312714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263128, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263128, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99257 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263136 q = 1) (hb : d312715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263136, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263136, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263137 q = 1) (hb : d312716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263137, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263137, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263138 q = 1) (hb : d312717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263138, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263138, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263139 q = 1) (hb : d312718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263139, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263139, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263140 q = 1) (hb : d312719 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263140, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263140, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99259 (p : Pattern) (ha : d263146 p = 1) (hb : d312725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263141 q = 1) (hb : d312720 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263141, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263141, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99258 q ha hb
  have h2 (q : Pattern) (ha : d263142 q = 1) (hb : d312721 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263142, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263142, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263143 q = 1) (hb : d312722 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263143, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263143, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263144 q = 1) (hb : d312723 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263144, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263144, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263145 q = 1) (hb : d312724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263145, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263145, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263146 q = 1) (hb : d312725 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263146, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263146, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99260 (p : Pattern) (ha : d263364 p = 1) (hb : d312026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263250 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99080 q ha hb
    | true =>
      simp only [d263250, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99081 q ha hb
  have h5 (q : Pattern) (ha : d263332 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263332, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263361 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263361, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263362 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263362, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263363 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263363, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263364 q = 1) (hb : d312026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263364, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263364, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99261 (p : Pattern) (ha : d263385 p = 1) (hb : d312036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263250 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99080 q ha hb
    | true =>
      simp only [d263250, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99081 q ha hb
  have h4 (q : Pattern) (ha : d263332 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263332, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263361 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263361, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263362 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263362, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263363 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263363, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263375 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263260 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99083 q ha hb
    | true =>
      simp only [d263260, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99084 q ha hb
  have h13 (q : Pattern) (ha : d263378 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263378, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263382 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263382, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263383 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263383, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263383, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263384 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263384, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263384, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263385 q = 1) (hb : d312036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263385, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263385, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99262 (p : Pattern) (ha : d263405 p = 1) (hb : d312731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263260 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99083 q ha hb
    | true =>
      simp only [d263260, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99084 q ha hb
  have h3 (q : Pattern) (ha : d263378 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263378, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263382 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263382, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263403 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263403, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263403, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263404 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263404, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263404, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263405 q = 1) (hb : d312731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263405, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263405, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99263 (p : Pattern) (ha : d263537 p = 1) (hb : d312742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263506 q = 1) (hb : d312737 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263506, d312737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99125 q ha hb
    | true =>
      simp only [d263506, d312737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99131 q ha hb
  have h3 (q : Pattern) (ha : d263507 q = 1) (hb : d312738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263507, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263507, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263534 q = 1) (hb : d312739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263534, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263534, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263535 q = 1) (hb : d312740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263535, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263535, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263536 q = 1) (hb : d312741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263536, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263536, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263537 q = 1) (hb : d312742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263537, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263537, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99264 (p : Pattern) (ha : d263550 p = 1) (hb : d312748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263268 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263386 q = 1) (hb : d312037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263386, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99260 q ha hb
    | true =>
      simp only [d263386, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99261 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263400 q = 1) (hb : d312038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263400, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263400, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263401 q = 1) (hb : d312729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263401, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263401, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263402 q = 1) (hb : d312730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263402, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263402, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263406 q = 1) (hb : d312732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263406, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263406, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99262 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263408 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263409 q = 1) (hb : d312733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263409, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263409, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263410 q = 1) (hb : d312734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263410, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263410, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263411 q = 1) (hb : d312735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263411, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263411, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263412 q = 1) (hb : d312736 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263412, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263412, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263538 q = 1) (hb : d312743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263538, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263538, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99263 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263546 q = 1) (hb : d312744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263546, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263546, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263547 q = 1) (hb : d312745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263547, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263547, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263548 q = 1) (hb : d312746 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263548, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263548, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263549 q = 1) (hb : d312747 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263549, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263549, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263550 q = 1) (hb : d312748 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263550, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263550, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99265 (p : Pattern) (ha : d263556 p = 1) (hb : d312754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263551 q = 1) (hb : d312749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263551, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263551, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99264 q ha hb
  have h2 (q : Pattern) (ha : d263552 q = 1) (hb : d312750 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263552, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263552, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263553 q = 1) (hb : d312751 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263553, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263553, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263554 q = 1) (hb : d312752 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263554, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263554, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263555 q = 1) (hb : d312753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263555, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263555, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263556 q = 1) (hb : d312754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263556, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263556, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99266 (p : Pattern) (ha : d44504 p = 1) (hb : d263768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44499 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99147 q ha hb
    | true =>
      simp only [d44499, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99148 q ha hb
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d263728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d263765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d263766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d263767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d263768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d263768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d263768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99267 (p : Pattern) (ha : d44514 p = 1) (hb : d263790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44499 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99147 q ha hb
    | true =>
      simp only [d44499, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99148 q ha hb
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d263728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d263765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d263766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d263767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44509 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99150 q ha hb
    | true =>
      simp only [d44509, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99151 q ha hb
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d263783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d263787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d263788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d263788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d263788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d263789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d263789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d263789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d263790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d263790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d263790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99268 (p : Pattern) (ha : d263815 p = 1) (hb : d309695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44509 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99150 q ha hb
    | true =>
      simp only [d44509, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99151 q ha hb
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d263783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d263787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d263813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d263813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d263813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d263814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d263814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d263814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263815 q = 1) (hb : d309695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro99269 (p : Pattern) (ha : d44723 p = 1) (hb : d263905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d263863 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d263863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99186 q ha hb
    | true =>
      simp only [d44703, d263863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99158 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d263864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d263864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d263864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d263865 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d263865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d263865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d263872 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d263872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99158 q ha hb
    | true =>
      simp only [d44713, d263872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99188 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d263873 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d263873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d263873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d263874 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d263874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d263874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d263875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d263875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d263875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44713 q = 1) (hb : d263891 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d263891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99158 q ha hb
    | true =>
      simp only [d44713, d263891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99159 q ha hb
  have h9 (q : Pattern) (ha : d44714 q = 1) (hb : d263892 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d263892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d263892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44715 q = 1) (hb : d263893 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d263893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d263893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44721 q = 1) (hb : d263894 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d263894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44721, d263894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44722 q = 1) (hb : d263904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44722, d263904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44722, d263904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44723 q = 1) (hb : d263905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44723, d263905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44723, d263905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro99270 (p : Pattern) (ha : d44737 p = 1) (hb : d263911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44724 q = 1) (hb : d263906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d263906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99269 q ha hb
    | true =>
      simp only [d44724, d263906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44725 q = 1) (hb : d263907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d263907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d263907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44732 q = 1) (hb : d263897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d263897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99160 q ha hb
    | true =>
      simp only [d44732, d263897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44733 q = 1) (hb : d263898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d263898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d263898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44734 q = 1) (hb : d263908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44734, d263908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44734, d263908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44735 q = 1) (hb : d263909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44735, d263909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44735, d263909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44736 q = 1) (hb : d263910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44736, d263910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44736, d263910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44737 q = 1) (hb : d263911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44737, d263911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44737, d263911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro99271 (p : Pattern) (ha : d44471 p = 1) (hb : d263922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44451 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44451, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99136 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5128 q = 1) (hb : d263917 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d263917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5128, d263917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h4 (q : Pattern) (ha : d44452 q = 1) (hb : d263918 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, d263918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44452, d263918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44453 q = 1) (hb : d263919 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, d263919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44453, d263919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44454 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99136 q ha hb
    | true =>
      simp only [d44454, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44455 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44455, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44456 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44456, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44457 q = 1) (hb : d263920 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, d263920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44457, d263920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44458 q = 1) (hb : d263921 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, d263921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44458, d263921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44471 q = 1) (hb : d263922 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44471, d263922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44471, d263922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro99272 (p : Pattern) (ha : d44712 p = 1) (hb : d263928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44692 q = 1) (hb : d263857 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d263857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d263857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99139 q ha hb
  have h2 (q : Pattern) (ha : d44460 q = 1) (hb : d263616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d263616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99139 q ha hb
    | true =>
      simp only [d44460, d263616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44693 q = 1) (hb : d263858 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d263858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44693, d263858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44461 q = 1) (hb : d263617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d263617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44461, d263617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44694 q = 1) (hb : d263859 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d263859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44694, d263859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44695 q = 1) (hb : d263860 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d263860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44695, d263860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44701 q = 1) (hb : d263889 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d263889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44701, d263889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44707 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44707, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44707, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99142 q ha hb
  have h9 (q : Pattern) (ha : d44472 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99142 q ha hb
    | true =>
      simp only [d44472, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44708 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44708, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44708, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44472 q = 1) (hb : d263923 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, d263923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99271 q ha hb
    | true =>
      simp only [d44472, d263923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44473 q = 1) (hb : d263924 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, d263924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44473, d263924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44709 q = 1) (hb : d263925 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44709, d263925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44709, d263925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44710 q = 1) (hb : d263926 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44710, d263926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44710, d263926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44711 q = 1) (hb : d263927 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44711, d263927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44711, d263927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44712 q = 1) (hb : d263928 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44712, d263928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44712, d263928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro99273 (p : Pattern) (ha : d44731 p = 1) (hb : d263934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44713 q = 1) (hb : d263929 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d263929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99158 q ha hb
    | true =>
      simp only [d44713, d263929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99272 q ha hb
  have h2 (q : Pattern) (ha : d44714 q = 1) (hb : d263930 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d263930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d263930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44715 q = 1) (hb : d263931 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d263931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d263931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44721 q = 1) (hb : d263932 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d263932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44721, d263932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44730 q = 1) (hb : d263933 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44730, d263933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44730, d263933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44731 q = 1) (hb : d263934 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44731, d263934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44731, d263934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99274 (p : Pattern) (ha : d44813 p = 1) (hb : d263940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44732 q = 1) (hb : d263935 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d263935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99273 q ha hb
    | true =>
      simp only [d44732, d263935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44733 q = 1) (hb : d263936 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d263936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d263936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44810 q = 1) (hb : d263937 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44810, d263937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44810, d263937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44811 q = 1) (hb : d263938 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44811, d263938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44811, d263938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44812 q = 1) (hb : d263939 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44812, d263939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44812, d263939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44813 q = 1) (hb : d263940 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44813, d263940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44813, d263940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99275 (p : Pattern) (ha : d263972 p = 1) (hb : d309706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263903 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263941 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263941, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99270 q hb ha
    | true =>
      simp only [d263941, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99274 q hb ha
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d309702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263942, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263969 q = 1) (hb : d309703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263970 q = 1) (hb : d309704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263971 q = 1) (hb : d309705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263972 q = 1) (hb : d309706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99276 (p : Pattern) (ha : d263989 p = 1) (hb : d309712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d263791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d263791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99266 q ha hb
    | true =>
      simp only [d44515, d263791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d263810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d263810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d263810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263811 q = 1) (hb : d309693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263811, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263812 q = 1) (hb : d309694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263812, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263816 q = 1) (hb : d309696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263816, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99268 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263819 q = 1) (hb : d309697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263819, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263820 q = 1) (hb : d309698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263820, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263821 q = 1) (hb : d309699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263821, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263822 q = 1) (hb : d309700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263822, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263973 q = 1) (hb : d309707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263973, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99275 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263985 q = 1) (hb : d309708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263985, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263986 q = 1) (hb : d309709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263986, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263987 q = 1) (hb : d309710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263987, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263988 q = 1) (hb : d309711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263988, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263989 q = 1) (hb : d309712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263989, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99277 (p : Pattern) (ha : d263995 p = 1) (hb : d309718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d309713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99276 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d309714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d309715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d309716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d309717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d309718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99278 (p : Pattern) (ha : d264001 p = 1) (hb : d312760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d312671 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99241 q ha hb
    | true =>
      simp only [d262468, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99247 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d312698 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99253 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d312699 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d312726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99259 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d312727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d312728 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d312755 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99265 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d312756 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d312757 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d312758 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99277 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d312759 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d312760 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro99279 (p : Pattern) (ha : d264007 p = 1) (hb : d312766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d312761 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99278 q ha hb
    | true =>
      simp only [d264002, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d312762 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d312763 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d312764 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d312765 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d312766 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99280 (p : Pattern) (ha : d264013 p = 1) (hb : d312772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d312767 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99279 q ha hb
    | true =>
      simp only [d264008, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d312768 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d312769 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d312770 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d312771 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d312772 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99281 (p : Pattern) (ha : d264019 p = 1) (hb : d312778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d312773 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99280 q ha hb
    | true =>
      simp only [d264014, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d312774 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d312775 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d312776 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d312777 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d312778 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99282 (p : Pattern) (ha : d264025 p = 1) (hb : d312784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d312779 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99281 q ha hb
    | true =>
      simp only [d264020, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d312780 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d312781 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d312782 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d312783 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d312784 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99283 (p : Pattern) (ha : d264031 p = 1) (hb : d312790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d312785 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99282 q ha hb
    | true =>
      simp only [d264026, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d312786 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d312787 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d312788 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d312789 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d312790 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99284 (p : Pattern) (ha : d264037 p = 1) (hb : d312796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d312791 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99283 q ha hb
    | true =>
      simp only [d264032, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d312792 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d312793 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d312794 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d312795 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d312796 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99285 (p : Pattern) (ha : d264043 p = 1) (hb : d312802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d312797 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99284 q ha hb
    | true =>
      simp only [d264038, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d312798 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d312799 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d312800 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d312801 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d312802 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99286 (p : Pattern) (ha : d265953 p = 1) (hb : d310865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310801 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265949 q = 1) (hb : d310861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265949, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265950 q = 1) (hb : d310862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265950, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265951 q = 1) (hb : d310863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265951, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265952 q = 1) (hb : d310864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265952, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265953 q = 1) (hb : d310865 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99287 (p : Pattern) (ha : d265958 p = 1) (hb : d310872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310801 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265949 q = 1) (hb : d310861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265949, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265950 q = 1) (hb : d310862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265950, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265951 q = 1) (hb : d310863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265951, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265952 q = 1) (hb : d310864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265952, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33403 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33407 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d310808 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265954 q = 1) (hb : d310868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265954, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265955 q = 1) (hb : d310869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265955, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265956 q = 1) (hb : d310870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265956, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265957 q = 1) (hb : d310871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265957, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265958 q = 1) (hb : d310872 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265958, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99288 (p : Pattern) (ha : d265965 p = 1) (hb : d312622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265954 q = 1) (hb : d310868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265954, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d310869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265955, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d310870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d310871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d312622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99289 (p : Pattern) (ha : d265975 p = 1) (hb : d312632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265971 q = 1) (hb : d312628 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265971, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d312629 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265972, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d312630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d312631 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d312632 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99290 (p : Pattern) (ha : d265981 p = 1) (hb : d312638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265959 q = 1) (hb : d310873 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99286 q ha hb
    | true =>
      simp only [d265959, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99287 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265960 q = 1) (hb : d310874 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265960, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265961 q = 1) (hb : d312620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265961, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265962 q = 1) (hb : d312621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265962, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265966 q = 1) (hb : d312623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265966, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99288 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d265967 q = 1) (hb : d312624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265967, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d265968 q = 1) (hb : d312625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265968, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265969 q = 1) (hb : d312626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265969, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d265970 q = 1) (hb : d312627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265970, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265976 q = 1) (hb : d312633 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265976, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99289 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265977 q = 1) (hb : d312634 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265977, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265978 q = 1) (hb : d312635 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265978, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265979 q = 1) (hb : d312636 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265979, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d265980 q = 1) (hb : d312637 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265980, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d265981 q = 1) (hb : d312638 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265981, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99291 (p : Pattern) (ha : d265987 p = 1) (hb : d312644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d265944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66749 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d265945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d265946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d265947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d265948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d312639 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99290 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d312640 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d312641 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d312642 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d312643 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d312644 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d265987, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro99292 (p : Pattern) (ha : d265992 p = 1) (hb : d311036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d311031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265988 q = 1) (hb : d311032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265988, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265989 q = 1) (hb : d311033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265989, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265990 q = 1) (hb : d311034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265990, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265991 q = 1) (hb : d311035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265991, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265992 q = 1) (hb : d311036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99293 (p : Pattern) (ha : d265997 p = 1) (hb : d311046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d311031 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265988 q = 1) (hb : d311032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265988, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265989 q = 1) (hb : d311033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265989, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265990 q = 1) (hb : d311034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265990, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265991 q = 1) (hb : d311035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265991, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33663 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33668 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d311041 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265993 q = 1) (hb : d311042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265993, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265994 q = 1) (hb : d311043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265994, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265995 q = 1) (hb : d311044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265995, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265996 q = 1) (hb : d311045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265996, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265997 q = 1) (hb : d311046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265997, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99294 (p : Pattern) (ha : d266004 p = 1) (hb : d312647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d311041 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265993 q = 1) (hb : d311042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265993, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d311043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265994, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d311044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d311045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d312647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99295 (p : Pattern) (ha : d266014 p = 1) (hb : d312658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312653 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266010 q = 1) (hb : d312654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266010, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33793 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d312655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266011, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d312656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d312657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d312658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99296 (p : Pattern) (ha : d266020 p = 1) (hb : d312664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265998 q = 1) (hb : d311047 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99292 q ha hb
    | true =>
      simp only [d265998, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99293 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265999 q = 1) (hb : d311048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265999, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266000 q = 1) (hb : d312645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266000, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266001 q = 1) (hb : d312646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266001, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266005 q = 1) (hb : d312648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266005, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99294 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d33704 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266006 q = 1) (hb : d312649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266006, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266007 q = 1) (hb : d312650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266007, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266008 q = 1) (hb : d312651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266008, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266009 q = 1) (hb : d312652 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266009, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266015 q = 1) (hb : d312659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266015, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99295 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33809 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266016 q = 1) (hb : d312660 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266016, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266017 q = 1) (hb : d312661 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266017, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266018 q = 1) (hb : d312662 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266018, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266019 q = 1) (hb : d312663 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266019, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266020 q = 1) (hb : d312664 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266020, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99297 (p : Pattern) (ha : d266026 p = 1) (hb : d312670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d312665 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99296 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d312666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d312667 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d312668 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d312669 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d312670 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99298 (p : Pattern) (ha : d266032 p = 1) (hb : d311295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d311290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266028 q = 1) (hb : d311291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266028, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266029 q = 1) (hb : d311292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266029, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266030 q = 1) (hb : d311293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266030, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266031 q = 1) (hb : d311294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266031, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266032 q = 1) (hb : d311295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99299 (p : Pattern) (ha : d266037 p = 1) (hb : d311305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d311290 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266028 q = 1) (hb : d311291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266028, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266029 q = 1) (hb : d311292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266029, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266030 q = 1) (hb : d311293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266030, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266031 q = 1) (hb : d311294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266031, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34038 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266033 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266033, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266034 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266034, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266035 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266035, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266036 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266036, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266037 q = 1) (hb : d311305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266037, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99300 (p : Pattern) (ha : d266044 p = 1) (hb : d312674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266033 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266033, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266034, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d312674 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99301 (p : Pattern) (ha : d266054 p = 1) (hb : d312685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312680 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266050 q = 1) (hb : d312681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266050, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d312682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266051, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d312683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d312684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d312685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99302 (p : Pattern) (ha : d266060 p = 1) (hb : d312691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266038 q = 1) (hb : d311306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99298 q ha hb
    | true =>
      simp only [d266038, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99299 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34065 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266039 q = 1) (hb : d311307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266039, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266040 q = 1) (hb : d312672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266040, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266041 q = 1) (hb : d312673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266041, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266045 q = 1) (hb : d312675 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266045, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99300 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266046 q = 1) (hb : d312676 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266046, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266047 q = 1) (hb : d312677 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266047, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266048 q = 1) (hb : d312678 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266048, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266049 q = 1) (hb : d312679 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266049, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266055 q = 1) (hb : d312686 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266055, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99301 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266056 q = 1) (hb : d312687 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266056, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266057 q = 1) (hb : d312688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266057, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266058 q = 1) (hb : d312689 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266058, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266059 q = 1) (hb : d312690 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266059, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266060 q = 1) (hb : d312691 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266060, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99303 (p : Pattern) (ha : d266066 p = 1) (hb : d312697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266061 q = 1) (hb : d312692 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266061, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266061, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99302 q ha hb
  have h2 (q : Pattern) (ha : d266062 q = 1) (hb : d312693 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266062, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266062, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266063 q = 1) (hb : d312694 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266063, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266063, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266064 q = 1) (hb : d312695 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266064, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266064, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266065 q = 1) (hb : d312696 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266065, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266065, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266066 q = 1) (hb : d312697 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266066, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266066, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99304 (p : Pattern) (ha : d266073 p = 1) (hb : d311633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266069 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266069, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266070 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266070, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266071 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266071, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266072 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266072, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266073 q = 1) (hb : d311633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266073, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266073, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99305 (p : Pattern) (ha : d266078 p = 1) (hb : d311643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266069 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266069, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266070 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266070, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266071 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266071, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266072 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266072, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34544 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266074 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266074, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266075 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266075, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266076 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266076, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266076, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266077 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266077, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266077, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266078 q = 1) (hb : d311643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266078, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266078, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99306 (p : Pattern) (ha : d266085 p = 1) (hb : d312702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266074 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266074, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266075 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266075, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266083 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266083, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266083, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266084 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266084, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266084, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266085 q = 1) (hb : d312702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266085, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266085, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99307 (p : Pattern) (ha : d266095 p = 1) (hb : d312713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266091 q = 1) (hb : d312709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266091, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266091, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266092 q = 1) (hb : d312710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266092, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266092, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266093 q = 1) (hb : d312711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266093, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266093, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266094 q = 1) (hb : d312712 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266094, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266094, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266095 q = 1) (hb : d312713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266095, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266095, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99308 (p : Pattern) (ha : d266101 p = 1) (hb : d312719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266079 q = 1) (hb : d311644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266079, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99304 q ha hb
    | true =>
      simp only [d266079, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99305 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266080 q = 1) (hb : d311645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266080, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266080, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266081 q = 1) (hb : d312700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266081, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266081, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266082 q = 1) (hb : d312701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266082, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266082, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266086 q = 1) (hb : d312703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266086, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266086, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99306 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34585 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266087 q = 1) (hb : d312704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266087, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266087, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266088 q = 1) (hb : d312705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266088, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266088, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266089 q = 1) (hb : d312706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266089, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266089, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266090 q = 1) (hb : d312707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266090, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266090, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266096 q = 1) (hb : d312714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266096, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266096, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99307 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266097 q = 1) (hb : d312715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266097, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266097, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266098 q = 1) (hb : d312716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266098, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266098, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266099 q = 1) (hb : d312717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266099, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266099, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266100 q = 1) (hb : d312718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266100, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266100, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266101 q = 1) (hb : d312719 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266101, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266101, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99309 (p : Pattern) (ha : d266107 p = 1) (hb : d312725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266102 q = 1) (hb : d312720 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266102, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266102, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99308 q ha hb
  have h2 (q : Pattern) (ha : d266103 q = 1) (hb : d312721 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266103, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266103, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266104 q = 1) (hb : d312722 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266104, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266104, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266105 q = 1) (hb : d312723 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266105, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266105, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266106 q = 1) (hb : d312724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266106, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266106, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266107 q = 1) (hb : d312725 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266107, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266107, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99310 (p : Pattern) (ha : d266115 p = 1) (hb : d312026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266111 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266111, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266112 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266112, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266113 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266113, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266114 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266114, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266115 q = 1) (hb : d312026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266115, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266115, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99311 (p : Pattern) (ha : d266120 p = 1) (hb : d312036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266111 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266111, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266112 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266112, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266113 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266113, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266114 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266114, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35112 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35117 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266116 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266116, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266117 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266117, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266118 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266118, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266118, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266119 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266119, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266119, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266120 q = 1) (hb : d312036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266120, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266120, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99312 (p : Pattern) (ha : d266127 p = 1) (hb : d312731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266116 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266116, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266117 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266117, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266125 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266125, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266125, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266126 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266126, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266126, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266127 q = 1) (hb : d312731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266127, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266127, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99313 (p : Pattern) (ha : d266137 p = 1) (hb : d312742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266133 q = 1) (hb : d312738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266133, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266133, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266134 q = 1) (hb : d312739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266134, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266134, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266135 q = 1) (hb : d312740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266135, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266135, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266136 q = 1) (hb : d312741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266136, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266136, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266137 q = 1) (hb : d312742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266137, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266137, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99314 (p : Pattern) (ha : d266143 p = 1) (hb : d312748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266121 q = 1) (hb : d312037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266121, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99310 q ha hb
    | true =>
      simp only [d266121, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99311 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266122 q = 1) (hb : d312038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266122, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266122, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266123 q = 1) (hb : d312729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266123, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266123, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266124 q = 1) (hb : d312730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266124, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266124, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266128 q = 1) (hb : d312732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266128, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266128, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99312 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35153 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266129 q = 1) (hb : d312733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266129, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266129, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266130 q = 1) (hb : d312734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266130, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266130, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266131 q = 1) (hb : d312735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266131, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266131, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266132 q = 1) (hb : d312736 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266132, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266132, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266138 q = 1) (hb : d312743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266138, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266138, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99313 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266139 q = 1) (hb : d312744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266139, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266139, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266140 q = 1) (hb : d312745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266140, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266140, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266141 q = 1) (hb : d312746 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266141, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266141, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266142 q = 1) (hb : d312747 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266142, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266142, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266143 q = 1) (hb : d312748 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266143, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266143, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99315 (p : Pattern) (ha : d266149 p = 1) (hb : d312754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266144 q = 1) (hb : d312749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266144, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266144, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99314 q ha hb
  have h2 (q : Pattern) (ha : d266145 q = 1) (hb : d312750 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266145, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266145, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266146 q = 1) (hb : d312751 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266146, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266146, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266147 q = 1) (hb : d312752 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266147, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266147, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266148 q = 1) (hb : d312753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266148, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266148, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266149 q = 1) (hb : d312754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266149, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266149, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99316 (p : Pattern) (ha : d44504 p = 1) (hb : d266158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d266154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d266155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d266156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d266157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d266158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d266158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d266158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99317 (p : Pattern) (ha : d44514 p = 1) (hb : d266163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d266154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d266155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d266156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d266157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35679 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35684 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d266159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d266160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d266161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d266161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d266161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d266162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d266162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d266162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d266163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d266163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d266163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99318 (p : Pattern) (ha : d266170 p = 1) (hb : d309695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d266159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d266160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d266168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d266168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d266168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d266169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d266169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d266169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266170 q = 1) (hb : d309695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266170, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266170, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro99319 (p : Pattern) (ha : d266180 p = 1) (hb : d309706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266176 q = 1) (hb : d309702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266176, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266176, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266177 q = 1) (hb : d309703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266177, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266177, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266178 q = 1) (hb : d309704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266178, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266178, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266179 q = 1) (hb : d309705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266179, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266179, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266180 q = 1) (hb : d309706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266180, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266180, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99320 (p : Pattern) (ha : d266186 p = 1) (hb : d309712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d266164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d266164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99316 q ha hb
    | true =>
      simp only [d44515, d266164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99317 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35717 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d266165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d266165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d266165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266166 q = 1) (hb : d309693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266166, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266166, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266167 q = 1) (hb : d309694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266167, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266167, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266171 q = 1) (hb : d309696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266171, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266171, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99318 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35726 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266172 q = 1) (hb : d309697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266172, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266172, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266173 q = 1) (hb : d309698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266173, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266173, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266174 q = 1) (hb : d309699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266174, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266174, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266175 q = 1) (hb : d309700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266175, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266175, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266181 q = 1) (hb : d309707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266181, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266181, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99319 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266182 q = 1) (hb : d309708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266182, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266182, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266183 q = 1) (hb : d309709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266183, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266183, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266184 q = 1) (hb : d309710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266184, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266184, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266185 q = 1) (hb : d309711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266185, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266185, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266186 q = 1) (hb : d309712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266186, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266186, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99321 (p : Pattern) (ha : d266192 p = 1) (hb : d309718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266187 q = 1) (hb : d309713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266187, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266187, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99320 q ha hb
  have h2 (q : Pattern) (ha : d266188 q = 1) (hb : d309714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266188, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266188, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266189 q = 1) (hb : d309715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266189, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266189, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266190 q = 1) (hb : d309716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266190, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266190, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266191 q = 1) (hb : d309717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266191, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266191, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266192 q = 1) (hb : d309718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266192, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266192, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99322 (p : Pattern) (ha : d266198 p = 1) (hb : d312760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d266027 q = 1) (hb : d312671 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266027, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99291 q ha hb
    | true =>
      simp only [d266027, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99297 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d266067 q = 1) (hb : d312698 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266067, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266067, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99303 q ha hb
  have h3 (q : Pattern) (ha : d266068 q = 1) (hb : d312699 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266068, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266068, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266108 q = 1) (hb : d312726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266108, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266108, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99309 q ha hb
  have h5 (q : Pattern) (ha : d266109 q = 1) (hb : d312727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266109, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266109, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266110 q = 1) (hb : d312728 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266110, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266110, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266150 q = 1) (hb : d312755 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266150, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266150, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99315 q ha hb
  have h8 (q : Pattern) (ha : d266151 q = 1) (hb : d312756 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266151, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266151, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266152 q = 1) (hb : d312757 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266152, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266152, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266153 q = 1) (hb : d312758 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266153, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266153, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266193 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266193, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266193, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99321 q ha hb
  have h12 (q : Pattern) (ha : d266194 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266194, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266194, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266195 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266195, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266195, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266196 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266196, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266196, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266197 q = 1) (hb : d312759 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d266197, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266197, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d266198 q = 1) (hb : d312760 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d266198, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266198, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro99323 (p : Pattern) (ha : d266204 p = 1) (hb : d312766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266199 q = 1) (hb : d312761 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d266199, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99322 q ha hb
    | true =>
      simp only [d266199, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266200 q = 1) (hb : d312762 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d266200, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266200, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266201 q = 1) (hb : d312763 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d266201, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266201, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266202 q = 1) (hb : d312764 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d266202, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266202, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266203 q = 1) (hb : d312765 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d266203, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266203, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266204 q = 1) (hb : d312766 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d266204, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266204, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99324 (p : Pattern) (ha : d266210 p = 1) (hb : d312772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266205 q = 1) (hb : d312767 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d266205, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99323 q ha hb
    | true =>
      simp only [d266205, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266206 q = 1) (hb : d312768 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d266206, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266206, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266207 q = 1) (hb : d312769 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d266207, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266207, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266208 q = 1) (hb : d312770 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d266208, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266208, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266209 q = 1) (hb : d312771 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d266209, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266209, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266210 q = 1) (hb : d312772 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d266210, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266210, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99325 (p : Pattern) (ha : d266216 p = 1) (hb : d312778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266211 q = 1) (hb : d312773 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d266211, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99324 q ha hb
    | true =>
      simp only [d266211, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266212 q = 1) (hb : d312774 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d266212, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266212, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266213 q = 1) (hb : d312775 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d266213, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266213, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266214 q = 1) (hb : d312776 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d266214, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266214, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266215 q = 1) (hb : d312777 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d266215, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266215, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266216 q = 1) (hb : d312778 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d266216, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266216, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99326 (p : Pattern) (ha : d266222 p = 1) (hb : d312784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266217 q = 1) (hb : d312779 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d266217, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99325 q ha hb
    | true =>
      simp only [d266217, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266218 q = 1) (hb : d312780 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d266218, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266218, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266219 q = 1) (hb : d312781 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d266219, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266219, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266220 q = 1) (hb : d312782 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d266220, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266220, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266221 q = 1) (hb : d312783 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d266221, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266221, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266222 q = 1) (hb : d312784 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d266222, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266222, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99327 (p : Pattern) (ha : d266228 p = 1) (hb : d312790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266223 q = 1) (hb : d312785 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d266223, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99326 q ha hb
    | true =>
      simp only [d266223, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266224 q = 1) (hb : d312786 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d266224, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266224, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266225 q = 1) (hb : d312787 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d266225, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266225, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266226 q = 1) (hb : d312788 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d266226, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266226, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266227 q = 1) (hb : d312789 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d266227, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266227, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266228 q = 1) (hb : d312790 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d266228, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266228, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99328 (p : Pattern) (ha : d266234 p = 1) (hb : d312796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266229 q = 1) (hb : d312791 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d266229, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99327 q ha hb
    | true =>
      simp only [d266229, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266230 q = 1) (hb : d312792 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d266230, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266230, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266231 q = 1) (hb : d312793 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d266231, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266231, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266232 q = 1) (hb : d312794 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d266232, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266232, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266233 q = 1) (hb : d312795 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d266233, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266233, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266234 q = 1) (hb : d312796 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d266234, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266234, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99329 (p : Pattern) (ha : d266240 p = 1) (hb : d312802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266235 q = 1) (hb : d312797 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d266235, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99328 q ha hb
    | true =>
      simp only [d266235, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266236 q = 1) (hb : d312798 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d266236, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266236, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266237 q = 1) (hb : d312799 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d266237, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266237, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266238 q = 1) (hb : d312800 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d266238, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266238, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266239 q = 1) (hb : d312801 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d266239, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266239, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266240 q = 1) (hb : d312802 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d266240, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266240, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro99330 (p : Pattern) (ha : d14 p = 1) (hb : d10054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d2005 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d2006 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99331 (p : Pattern) (ha : d14 p = 1) (hb : d32698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d2001 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d2002 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d32698 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99332 (p : Pattern) (ha : d14 p = 1) (hb : d44444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d35372 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99331 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d10055 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99330 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d35373 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44444 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro99333 (p : Pattern) (ha : d14 p = 1) (hb : d1563 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1519 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d1531 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d1547 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro99334 (p : Pattern) (ha : d14 p = 1) (hb : d44450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1519 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d34366 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d34367 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d34367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44450 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99335 (p : Pattern) (ha : d14 p = 1) (hb : d44459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d35372 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99331 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d10055 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99330 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d35373 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44451 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99334 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d5128 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99333 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44452 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44453 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44454 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99334 q ha hb
    | true =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d1564 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99333 q ha hb
    | true =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44455 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d44456 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44457 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d44458 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d44459 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro99336 (p : Pattern) (ha : d14 p = 1) (hb : d44465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44462 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44463 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44464 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44465 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99337 (p : Pattern) (ha : d14 p = 1) (hb : d44467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44462 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44463 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44464 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44466 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44467 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99338 (p : Pattern) (ha : d14 p = 1) (hb : d44471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44451 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99334 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d5128 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99333 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44452 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44453 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44454 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99334 q ha hb
    | true =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d1564 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99333 q ha hb
    | true =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44455 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44456 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44457 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44458 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro99339 (p : Pattern) (ha : d14 p = 1) (hb : d44477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44462 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44463 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44466 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99338 q ha hb
    | true =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44474 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44475 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44476 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44477 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99340 (p : Pattern) (ha : d14 p = 1) (hb : d44484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44468 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99336 q ha hb
    | true =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44469 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44470 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44478 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99339 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44479 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44480 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44481 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44482 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44483 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44484 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro99341 (p : Pattern) (ha : d14 p = 1) (hb : d44488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44478 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99339 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44479 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44480 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44482 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44488 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99342 (p : Pattern) (ha : d14 p = 1) (hb : d44494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44492 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44493 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44494 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99343 (p : Pattern) (ha : d14 p = 1) (hb : d44498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44497 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44498 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99344 (p : Pattern) (ha : d14 p = 1) (hb : d44504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99342 q ha hb
    | true =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99343 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99345 (p : Pattern) (ha : d14 p = 1) (hb : d44507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44492 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44493 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99346 (p : Pattern) (ha : d14 p = 1) (hb : d44508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44497 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99347 (p : Pattern) (ha : d14 p = 1) (hb : d44514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99342 q ha hb
    | true =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99343 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99345 q ha hb
    | true =>
      simp only [d44509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99346 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99348 (p : Pattern) (ha : d14 p = 1) (hb : d44665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99342 q ha hb
    | true =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99343 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44660 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99343 q ha hb
    | true =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99349 (p : Pattern) (ha : d14 p = 1) (hb : d44671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44660 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99343 q ha hb
    | true =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99346 q ha hb
    | true =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99350 (p : Pattern) (ha : d14 p = 1) (hb : d44680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99346 q ha hb
    | true =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99351 (p : Pattern) (ha : d14 p = 1) (hb : d44702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44686 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44688 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44689 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44693 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44694 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44695 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d44701 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44702 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99352 (p : Pattern) (ha : d14 p = 1) (hb : d44712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44693 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44694 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44695 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44701 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99338 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99338 q ha hb
    | true =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44709 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44710 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d44711 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44712 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99353 (p : Pattern) (ha : d14 p = 1) (hb : d44731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44713 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99352 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44714 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44715 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44721 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44730 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44731 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99354 (p : Pattern) (ha : d14 p = 1) (hb : d44813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44732 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99353 q ha hb
    | true =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44733 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44810 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99355 (p : Pattern) (ha : d14 p = 1) (hb : d44819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99354 q ha hb
    | true =>
      simp only [d44814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99356 (p : Pattern) (ha : d14 p = 1) (hb : d44519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44492 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44518 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44519 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99357 (p : Pattern) (ha : d14 p = 1) (hb : d44521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99358 (p : Pattern) (ha : d14 p = 1) (hb : d44528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99359 (p : Pattern) (ha : d14 p = 1) (hb : d44531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44529 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44530 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44531 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99360 (p : Pattern) (ha : d14 p = 1) (hb : d44535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99361 (p : Pattern) (ha : d14 p = 1) (hb : d44541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99360 q ha hb
    | true =>
      simp only [d44536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99336 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44468 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99336 q ha hb
    | true =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44469 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44470 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44478 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99339 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44479 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44480 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44481 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44540 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44541 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro99362 (p : Pattern) (ha : d14 p = 1) (hb : d44547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44542 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99361 q ha hb
    | true =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44543 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99363 (p : Pattern) (ha : d14 p = 1) (hb : d44609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d35372 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99331 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d10055 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99330 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d35373 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44609 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99364 (p : Pattern) (ha : d14 p = 1) (hb : d44615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44462 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44463 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44464 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44610 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99363 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44611 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44612 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44613 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d44614 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44615 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99365 (p : Pattern) (ha : d14 p = 1) (hb : d44616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44610 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99363 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44611 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44612 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44613 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44614 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44616 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99366 (p : Pattern) (ha : d14 p = 1) (hb : d44622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44468 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99336 q ha hb
    | true =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44469 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44470 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44478 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99337 q ha hb
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99339 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44479 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44480 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44481 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99364 q ha hb
    | true =>
      simp only [d44617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99365 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44621 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44622 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro99367 (p : Pattern) (ha : d14 p = 1) (hb : d44628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99366 q ha hb
    | true =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99368 (p : Pattern) (ha : d14 p = 1) (hb : d309471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99356 q ha hb
    | true =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99357 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99358 q ha hb
    | true =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99359 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99362 q ha hb
    | true =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99342 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99367 q ha hb
    | true =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99369 (p : Pattern) (ha : d14 p = 1) (hb : d44635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44492 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44518 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99370 (p : Pattern) (ha : d14 p = 1) (hb : d44636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99371 (p : Pattern) (ha : d14 p = 1) (hb : d44641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99372 (p : Pattern) (ha : d14 p = 1) (hb : d44642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99341 q ha hb
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44529 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44530 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99373 (p : Pattern) (ha : d14 p = 1) (hb : d44646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44542 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99361 q ha hb
    | true =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44543 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99340 q ha hb
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44646 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99374 (p : Pattern) (ha : d14 p = 1) (hb : d44652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99366 q ha hb
    | true =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99375 (p : Pattern) (ha : d14 p = 1) (hb : d309476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99356 q ha hb
    | true =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99357 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99358 q ha hb
    | true =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99359 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99362 q ha hb
    | true =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99342 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99367 q ha hb
    | true =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99369 q ha hb
    | true =>
      simp only [d44637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99370 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d44638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d44639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d44640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d44643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99371 q ha hb
    | true =>
      simp only [d44643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99372 q ha hb
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d44644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d44645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d44645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99373 q ha hb
    | true =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99345 q ha hb
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d309472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14 q = 1) (hb : d44653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99374 q ha hb
    | true =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d14 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d14 q = 1) (hb : d309473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d14 q = 1) (hb : d309474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d14 q = 1) (hb : d309475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d14 q = 1) (hb : d309476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro99376 (p : Pattern) (ha : d14 p = 1) (hb : d309483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99373 q ha hb
    | true =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99345 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99374 q ha hb
    | true =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99377 (p : Pattern) (ha : d14 p = 1) (hb : d44691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44686 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44688 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44689 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44690 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44691 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99378 (p : Pattern) (ha : d14 p = 1) (hb : d44697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44686 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44688 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44689 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44690 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44693 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44694 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44695 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d44696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44697 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99379 (p : Pattern) (ha : d14 p = 1) (hb : d44718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44698 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99377 q ha hb
    | true =>
      simp only [d44698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99378 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44700 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44703 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99378 q ha hb
    | true =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44704 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44705 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44706 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44713 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99352 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44714 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44715 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44716 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44717 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44718 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro99380 (p : Pattern) (ha : d14 p = 1) (hb : d44723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44703 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99378 q ha hb
    | true =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44704 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44705 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44713 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99352 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44714 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44715 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44716 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44721 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44722 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro99381 (p : Pattern) (ha : d14 p = 1) (hb : d44729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44719 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99379 q ha hb
    | true =>
      simp only [d44719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44720 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44724 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99380 q ha hb
    | true =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44725 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44726 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44727 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44728 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44729 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99382 (p : Pattern) (ha : d14 p = 1) (hb : d44737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44724 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99380 q ha hb
    | true =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44725 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44732 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99353 q ha hb
    | true =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44733 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44734 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99383 (p : Pattern) (ha : d14 p = 1) (hb : d44789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44686 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44445 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99332 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44446 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44688 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44689 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44460 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99335 q ha hb
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44693 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44461 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44694 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44695 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d44784 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99363 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44610 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99363 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d44785 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d44611 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d44786 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d44787 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d44788 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d44789 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro99384 (p : Pattern) (ha : d14 p = 1) (hb : d44790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44784 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99363 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44610 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99363 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44785 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44611 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44786 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44787 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44788 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44790 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99385 (p : Pattern) (ha : d14 p = 1) (hb : d44796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44703 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99378 q ha hb
    | true =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44704 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44705 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44713 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99351 q ha hb
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99352 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44714 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44715 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44716 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99383 q ha hb
    | true =>
      simp only [d44791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99384 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d44793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44795 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d44796 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro99386 (p : Pattern) (ha : d14 p = 1) (hb : d44802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99385 q ha hb
    | true =>
      simp only [d44797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44799 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44800 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44801 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44802 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99387 (p : Pattern) (ha : d14 p = 1) (hb : d309493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99381 q ha hb
    | true =>
      simp only [d44738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99382 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99386 q ha hb
    | true =>
      simp only [d44803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99388 (p : Pattern) (ha : d14 p = 1) (hb : d309499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99344 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99344 q ha hb
    | true =>
      simp only [d44515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99347 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99368 q ha hb
    | true =>
      simp only [d309477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99375 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99348 q ha hb
    | true =>
      simp only [d44672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99349 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d309480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99376 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d44681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99350 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d309494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99387 q ha hb
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d44820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99355 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d309495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d309496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d309497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d309498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d309499 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro99389 (p : Pattern) (ha : d14 p = 1) (hb : d309505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d309500 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99388 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309501 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d309502 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d309503 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309504 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309505 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99390 (p : Pattern) (ha : d14 p = 1) (hb : d42249 p = 1) : d357601 p = 1 := by
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
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42246 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42247 q = 1) : d357599 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d357599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42247, d357599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d16 q = 1) : d16 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42248 q = 1) : d357600 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d357600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42248, d357600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d17 q = 1) : d17 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42249 q = 1) : d357601 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42249, d357601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42249, d357601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99391 (p : Pattern) (ha : d14 p = 1) (hb : d42255 p = 1) : d357607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d21 q = 1) : d21 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42253 q = 1) : d357605 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d357605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42253, d357605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42254 q = 1) : d357606 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d357606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42254, d357606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d23 q = 1) : d23 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42255 q = 1) : d357607 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42255, d357607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42255, d357607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro99392 (p : Pattern) (ha : d14 p = 1) (hb : d42261 p = 1) : d357613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42256 q = 1) : d357608 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99391 q ha hb
    | true =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42257 q = 1) : d357609 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42258 q = 1) : d357610 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d357610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42258, d357610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42259 q = 1) : d357611 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d357611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42259, d357611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d28 q = 1) : d28 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42260 q = 1) : d357612 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42260, d357612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42260, d357612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d29 q = 1) : d29 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42261 q = 1) : d357613 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42261, d357613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42261, d357613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99393 (p : Pattern) (ha : d14 p = 1) (hb : d42267 p = 1) : d357619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d30 q = 1) : d30 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42262 q = 1) : d357614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
    | true =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42263 q = 1) : d357615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42264 q = 1) : d357616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d33 q = 1) : d33 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42265 q = 1) : d357617 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d357617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42265, d357617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d34 q = 1) : d34 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42266 q = 1) : d357618 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42266, d357618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42266, d357618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42267 q = 1) : d357619 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42267, d357619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42267, d357619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro99394 (p : Pattern) (ha : d14 p = 1) (hb : d42273 p = 1) : d357625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d38 q = 1) : d38 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42270 q = 1) : d357622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42271 q = 1) : d357623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42272 q = 1) : d357624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d357624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42272, d357624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42273 q = 1) : d357625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42273, d357625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42273, d357625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro99395 (p : Pattern) (ha : d14 p = 1) (hb : d309771 p = 1) : d357631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d120 q = 1) : d120 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d126 q = 1) : d126 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42 q = 1) : d42 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42274 q = 1) : d357626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
    | true =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309767 q = 1) : d357627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d357627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309767, d357627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44 q = 1) : d44 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309768 q = 1) : d357628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d357628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309768, d357628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309769 q = 1) : d357629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d357629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309769, d357629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309770 q = 1) : d357630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d357630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309770, d357630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d309771 q = 1) : d357631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309771, d357631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309771, d357631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99396 (p : Pattern) (ha : d14 p = 1) (hb : d42280 p = 1) : d357632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d38 q = 1) : d38 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42270 q = 1) : d357622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42271 q = 1) : d357623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42272 q = 1) : d357624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d357624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42272, d357624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42280 q = 1) : d357632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42280, d357632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42280, d357632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99397 (p : Pattern) (ha : d14 p = 1) (hb : d309776 p = 1) : d357638 p = 1 := by
  have h0 (q : Pattern) (ha : d14 q = 1) (hb : d120 q = 1) : d120 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d126 q = 1) : d126 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42 q = 1) : d42 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42274 q = 1) : d357626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
    | true =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309767 q = 1) : d357627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d357627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309767, d357627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44 q = 1) : d44 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309768 q = 1) : d357628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d357628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309768, d357628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309769 q = 1) : d357629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d357629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309769, d357629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309770 q = 1) : d357630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d357630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309770, d357630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d198 q = 1) : d198 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d202 q = 1) : d202 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d49 q = 1) : d49 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42281 q = 1) : d357633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99396 q ha hb
    | true =>
      simp only [d42281, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309772 q = 1) : d357634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d357634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309772, d357634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d51 q = 1) : d51 q = 1 := by
    exact hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309773 q = 1) : d357635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d357635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309773, d357635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d309774 q = 1) : d357636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309774, d357636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309774, d357636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d309775 q = 1) : d357637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309775, d357637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309775, d357637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d309776 q = 1) : d357638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309776, d357638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309776, d357638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99398 (p : Pattern) (ha : d14 p = 1) (hb : d309783 p = 1) : d357645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d49 q = 1) : d49 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42281 q = 1) : d357633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99396 q ha hb
    | true =>
      simp only [d42281, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d309772 q = 1) : d357634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d357634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309772, d357634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d51 q = 1) : d51 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309773 q = 1) : d357635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d357635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309773, d357635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309781 q = 1) : d357643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309781, d357643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309781, d357643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309782 q = 1) : d357644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309782, d357644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309782, d357644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309783 q = 1) : d357645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309783, d357645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309783, d357645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99399 (p : Pattern) (ha : d14 p = 1) (hb : d42304 p = 1) : d357656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42299 q = 1) : d357651 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d357651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42299, d357651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99391 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42256 q = 1) : d357608 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99391 q ha hb
    | true =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42300 q = 1) : d357652 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d357652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42300, d357652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42257 q = 1) : d357609 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42301 q = 1) : d357653 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d357653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42301, d357653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42302 q = 1) : d357654 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d357654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42302, d357654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d69 q = 1) : d69 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42303 q = 1) : d357655 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42303, d357655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42303, d357655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d70 q = 1) : d70 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42304 q = 1) : d357656 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42304, d357656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42304, d357656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99400 (p : Pattern) (ha : d14 p = 1) (hb : d42310 p = 1) : d357662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d71 q = 1) : d71 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42305 q = 1) : d357657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
    | true =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42306 q = 1) : d357658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42307 q = 1) : d357659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d74 q = 1) : d74 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42308 q = 1) : d357660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d357660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42308, d357660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d75 q = 1) : d75 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42309 q = 1) : d357661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42309, d357661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42309, d357661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42310 q = 1) : d357662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42310, d357662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42310, d357662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro99401 (p : Pattern) (ha : d14 p = 1) (hb : d42316 p = 1) : d357668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42311 q = 1) : d357663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d357663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99400 q ha hb
    | true =>
      simp only [d42311, d357663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42312 q = 1) : d357664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d357664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42312, d357664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d79 q = 1) : d79 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42313 q = 1) : d357665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42313, d357665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42313, d357665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42314 q = 1) : d357666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42314, d357666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42314, d357666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42315 q = 1) : d357667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42315, d357667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42315, d357667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42316 q = 1) : d357668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42316, d357668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42316, d357668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99402 (p : Pattern) (ha : d14 p = 1) (hb : d309793 p = 1) : d357674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d83 q = 1) : d83 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42317 q = 1) : d357669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d357669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99401 q ha hb
    | true =>
      simp only [d42317, d357669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d309789 q = 1) : d357670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309789, d357670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309789, d357670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d85 q = 1) : d85 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309790 q = 1) : d357671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309790, d357671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309790, d357671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309791 q = 1) : d357672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309791, d357672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309791, d357672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309792 q = 1) : d357673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309792, d357673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309792, d357673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309793 q = 1) : d357674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309793, d357674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309793, d357674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99403 (p : Pattern) (ha : d14 p = 1) (hb : d309799 p = 1) : d357680 p = 1 := by
  have h0 (q : Pattern) (ha : d14 q = 1) (hb : d114 q = 1) : d114 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d309777 q = 1) : d357639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309777, d357639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99395 q ha hb
    | true =>
      simp only [d309777, d357639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99397 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d214 q = 1) : d214 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d309778 q = 1) : d357640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309778, d357640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309778, d357640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309779 q = 1) : d357641 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309779, d357641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309779, d357641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309780 q = 1) : d357642 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309780, d357642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309780, d357642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309784 q = 1) : d357646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309784, d357646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309784, d357646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99398 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309785 q = 1) : d357647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309785, d357647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309785, d357647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309786 q = 1) : d357648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309786, d357648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309786, d357648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d309787 q = 1) : d357649 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309787, d357649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309787, d357649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309788 q = 1) : d357650 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309788, d357650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309788, d357650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309794 q = 1) : d357675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309794, d357675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309794, d357675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99402 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309795 q = 1) : d357676 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309795, d357676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309795, d357676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309796 q = 1) : d357677 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309796, d357677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309796, d357677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309797 q = 1) : d357678 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309797, d357678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309797, d357678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309798 q = 1) : d357679 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309798, d357679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309798, d357679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d309799 q = 1) : d357680 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309799, d357680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309799, d357680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro99404 (p : Pattern) (ha : d14 p = 1) (hb : d42338 p = 1) : d357690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42 q = 1) : d42 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42274 q = 1) : d357626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
    | true =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42334 q = 1) : d357686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42334, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42335 q = 1) : d357687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42336 q = 1) : d357688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42336, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42337 q = 1) : d357689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42337, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42338 q = 1) : d357690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42338, d357690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42338, d357690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro99405 (p : Pattern) (ha : d14 p = 1) (hb : d42345 p = 1) : d357697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42 q = 1) : d42 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42274 q = 1) : d357626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
    | true =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42334 q = 1) : d357686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42334, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42335 q = 1) : d357687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42336 q = 1) : d357688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42336, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42337 q = 1) : d357689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42337, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d49 q = 1) : d49 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42281 q = 1) : d357633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99396 q ha hb
    | true =>
      simp only [d42281, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42341 q = 1) : d357693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42341, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42342 q = 1) : d357694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42342, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42343 q = 1) : d357695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42343, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42344 q = 1) : d357696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42344, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42345 q = 1) : d357697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42345, d357697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42345, d357697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro99406 (p : Pattern) (ha : d14 p = 1) (hb : d42459 p = 1) : d357779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42 q = 1) : d42 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42274 q = 1) : d357626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
    | true =>
      simp only [d42274, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42334 q = 1) : d357686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42334, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42335 q = 1) : d357687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42336 q = 1) : d357688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42336, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42337 q = 1) : d357689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42337, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d103 q = 1) : d103 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42459 q = 1) : d357779 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42459, d357779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42459, d357779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99407 (p : Pattern) (ha : d14 p = 1) (hb : d42350 p = 1) : d357702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d38 q = 1) : d38 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42270 q = 1) : d357622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42271 q = 1) : d357623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42349 q = 1) : d357701 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d357701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42349, d357701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42350 q = 1) : d357702 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42350, d357702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42350, d357702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro99408 (p : Pattern) (ha : d14 p = 1) (hb : d42357 p = 1) : d357709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d38 q = 1) : d38 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42270 q = 1) : d357622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42355 q = 1) : d357707 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d357707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42355, d357707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42356 q = 1) : d357708 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d357708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42356, d357708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42357 q = 1) : d357709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42357, d357709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42357, d357709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro99409 (p : Pattern) (ha : d14 p = 1) (hb : d42363 p = 1) : d357714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42246 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42361 q = 1) : d44996 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42361, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42247 q = 1) : d357599 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d357599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42247, d357599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42362 q = 1) : d357713 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42362, d357713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42362, d357713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d16 q = 1) : d16 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42248 q = 1) : d357600 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d357600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42248, d357600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42363 q = 1) : d357714 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42363, d357714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42363, d357714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro99410 (p : Pattern) (ha : d14 p = 1) (hb : d42369 p = 1) : d357720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42364 q = 1) : d357715 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99409 q ha hb
    | true =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42365 q = 1) : d357716 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42366 q = 1) : d357717 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42367 q = 1) : d357718 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d357718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d357718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42368 q = 1) : d357719 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d357719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42368, d357719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d21 q = 1) : d21 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42253 q = 1) : d357605 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d357605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42253, d357605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42254 q = 1) : d357606 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d357606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42254, d357606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42369 q = 1) : d357720 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42369, d357720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42369, d357720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro99411 (p : Pattern) (ha : d14 p = 1) (hb : d42377 p = 1) : d357728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42375 q = 1) : d357726 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d357726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42375, d357726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42376 q = 1) : d357727 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d357727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42376, d357727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d23 q = 1) : d23 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42377 q = 1) : d357728 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42377, d357728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42377, d357728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99412 (p : Pattern) (ha : d14 p = 1) (hb : d42383 p = 1) : d357734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42370 q = 1) : d357721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99410 q ha hb
    | true =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42371 q = 1) : d357722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42372 q = 1) : d357723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d357723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42372, d357723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42373 q = 1) : d357724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d357724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d357724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42256 q = 1) : d357608 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99391 q ha hb
    | true =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42257 q = 1) : d357609 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42258 q = 1) : d357610 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d357610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42258, d357610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42259 q = 1) : d357611 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d357611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42259, d357611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42374 q = 1) : d357725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42374, d357725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42374, d357725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42378 q = 1) : d357729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
    | true =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42379 q = 1) : d357730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42380 q = 1) : d357731 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d357731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42380, d357731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42381 q = 1) : d357732 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d357732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42381, d357732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d28 q = 1) : d28 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42382 q = 1) : d357733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d357733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42382, d357733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42383 q = 1) : d357734 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42383, d357734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42383, d357734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro99413 (p : Pattern) (ha : d14 p = 1) (hb : d42389 p = 1) : d357740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42384 q = 1) : d357735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d357735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99412 q ha hb
    | true =>
      simp only [d42384, d357735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42385 q = 1) : d357736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d357736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42385, d357736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42386 q = 1) : d357737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d357737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42386, d357737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d30 q = 1) : d30 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42262 q = 1) : d357614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
    | true =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42263 q = 1) : d357615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42264 q = 1) : d357616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42387 q = 1) : d357738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d357738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d357738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d33 q = 1) : d33 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42265 q = 1) : d357617 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d357617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42265, d357617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42388 q = 1) : d357739 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42388, d357739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42388, d357739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42389 q = 1) : d357740 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42389, d357740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42389, d357740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro99414 (p : Pattern) (ha : d14 p = 1) (hb : d42395 p = 1) : d357746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42390 q = 1) : d357741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d357741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99413 q ha hb
    | true =>
      simp only [d42390, d357741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42391 q = 1) : d357742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d357742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42391, d357742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42392 q = 1) : d357743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d357743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d357743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42393 q = 1) : d357744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d357744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d357744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42394 q = 1) : d357745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d357745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d357745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42395 q = 1) : d357746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42395, d357746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42395, d357746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99415 (p : Pattern) (ha : d14 p = 1) (hb : d42430 p = 1) : d357752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42427 q = 1) : d357749 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d357749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d357749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42428 q = 1) : d357750 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d357750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d357750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42429 q = 1) : d357751 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d357751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d357751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42430 q = 1) : d357752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42430, d357752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42430, d357752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99416 (p : Pattern) (ha : d14 p = 1) (hb : d309809 p = 1) : d357758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d116 q = 1) : d116 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42351 q = 1) : d357703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d357703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99407 q ha hb
    | true =>
      simp only [d42351, d357703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42352 q = 1) : d357704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d357704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42352, d357704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42353 q = 1) : d357705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d357705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42353, d357705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42354 q = 1) : d357706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d357706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42354, d357706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d123 q = 1) : d123 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42358 q = 1) : d357710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d357710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99408 q ha hb
    | true =>
      simp only [d42358, d357710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42359 q = 1) : d357711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d357711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42359, d357711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42360 q = 1) : d357712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d357712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42360, d357712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42396 q = 1) : d357747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d357747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99414 q ha hb
    | true =>
      simp only [d42396, d357747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309805 q = 1) : d357748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d357748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309805, d357748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42431 q = 1) : d357753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d357753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99415 q ha hb
    | true =>
      simp only [d42431, d357753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42432 q = 1) : d357754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d357754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42432, d357754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309806 q = 1) : d357755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d357755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309806, d357755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309807 q = 1) : d357756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d357756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309807, d357756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309808 q = 1) : d357757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d357757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309808, d357757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d309809 q = 1) : d357758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d357758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309809, d357758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro99417 (p : Pattern) (ha : d14 p = 1) (hb : d42437 p = 1) : d357759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d38 q = 1) : d38 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42270 q = 1) : d357622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42271 q = 1) : d357623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d357623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42349 q = 1) : d357701 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d357701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42349, d357701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42437 q = 1) : d357759 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42437, d357759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42437, d357759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99418 (p : Pattern) (ha : d14 p = 1) (hb : d42442 p = 1) : d357764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d38 q = 1) : d38 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42270 q = 1) : d357622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d357622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42355 q = 1) : d357707 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d357707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42355, d357707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42356 q = 1) : d357708 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d357708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42356, d357708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42442 q = 1) : d357764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42442, d357764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42442, d357764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99419 (p : Pattern) (ha : d14 p = 1) (hb : d42446 p = 1) : d357768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42390 q = 1) : d357741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d357741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99413 q ha hb
    | true =>
      simp only [d42390, d357741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42391 q = 1) : d357742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d357742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42391, d357742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42392 q = 1) : d357743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d357743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d357743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42393 q = 1) : d357744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d357744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d357744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42394 q = 1) : d357745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d357745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d357745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42446 q = 1) : d357768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42446, d357768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42446, d357768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99420 (p : Pattern) (ha : d14 p = 1) (hb : d42451 p = 1) : d357771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42268 q = 1) : d357620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99393 q ha hb
    | true =>
      simp only [d42268, d357620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42269 q = 1) : d357621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d357621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42427 q = 1) : d357749 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d357749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d357749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42428 q = 1) : d357750 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d357750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d357750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42429 q = 1) : d357751 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d357751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d357751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42451 q = 1) : d357771 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42451, d357771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42451, d357771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99421 (p : Pattern) (ha : d14 p = 1) (hb : d309814 p = 1) : d357777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d116 q = 1) : d116 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42351 q = 1) : d357703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d357703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99407 q ha hb
    | true =>
      simp only [d42351, d357703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42352 q = 1) : d357704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d357704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42352, d357704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42353 q = 1) : d357705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d357705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42353, d357705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42354 q = 1) : d357706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d357706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42354, d357706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d123 q = 1) : d123 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42358 q = 1) : d357710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d357710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99408 q ha hb
    | true =>
      simp only [d42358, d357710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42359 q = 1) : d357711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d357711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42359, d357711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42360 q = 1) : d357712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d357712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42360, d357712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42396 q = 1) : d357747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d357747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99414 q ha hb
    | true =>
      simp only [d42396, d357747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99394 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309805 q = 1) : d357748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d357748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309805, d357748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42431 q = 1) : d357753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d357753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99415 q ha hb
    | true =>
      simp only [d42431, d357753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42432 q = 1) : d357754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d357754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42432, d357754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309806 q = 1) : d357755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d357755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309806, d357755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309807 q = 1) : d357756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d357756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309807, d357756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309808 q = 1) : d357757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d357757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309808, d357757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d194 q = 1) : d194 q = 1 := by
    exact hb
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42438 q = 1) : d357760 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42438, d357760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99417 q ha hb
    | true =>
      simp only [d42438, d357760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d42439 q = 1) : d357761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42439, d357761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42439, d357761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d42440 q = 1) : d357762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42440, d357762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42440, d357762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d42441 q = 1) : d357763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42441, d357763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42441, d357763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d199 q = 1) : d199 q = 1 := by
    exact hb
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d42443 q = 1) : d357765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42443, d357765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99418 q ha hb
    | true =>
      simp only [d42443, d357765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d14 q = 1) (hb : d42444 q = 1) : d357766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42444, d357766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42444, d357766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d14 q = 1) (hb : d42445 q = 1) : d357767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42445, d357767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42445, d357767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d14 q = 1) (hb : d42447 q = 1) : d357769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d357769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99419 q ha hb
    | true =>
      simp only [d42447, d357769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99396 q ha hb
  have h27 (q : Pattern) (ha : d14 q = 1) (hb : d309810 q = 1) : d357770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d357770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d309810, d357770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d14 q = 1) (hb : d42452 q = 1) : d357772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d357772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99420 q ha hb
    | true =>
      simp only [d42452, d357772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d14 q = 1) (hb : d42453 q = 1) : d357773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d357773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d42453, d357773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d14 q = 1) (hb : d309811 q = 1) : d357774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d357774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d309811, d357774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d14 q = 1) (hb : d309812 q = 1) : d357775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d357775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d309812, d357775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d14 q = 1) (hb : d309813 q = 1) : d357776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d357776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309813, d357776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d14 q = 1) (hb : d309814 q = 1) : d357777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d357777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309814, d357777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro99422 (p : Pattern) (ha : d14 p = 1) (hb : d309821 p = 1) : d357786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42447 q = 1) : d357769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d357769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99419 q ha hb
    | true =>
      simp only [d42447, d357769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99396 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309810 q = 1) : d357770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d357770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309810, d357770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42452 q = 1) : d357772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d357772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99420 q ha hb
    | true =>
      simp only [d42452, d357772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42453 q = 1) : d357773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d357773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42453, d357773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309811 q = 1) : d357774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d357774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309811, d357774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309819 q = 1) : d357784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d357784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309819, d357784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309820 q = 1) : d357785 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d357785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309820, d357785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309821 q = 1) : d357786 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d357786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309821, d357786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99423 (p : Pattern) (ha : d14 p = 1) (hb : d42482 p = 1) : d357802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42472 q = 1) : d357792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d357792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42472, d357792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99410 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42370 q = 1) : d357721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99410 q ha hb
    | true =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42473 q = 1) : d357793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d357793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d357793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42371 q = 1) : d357722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42474 q = 1) : d357794 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d357794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d357794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42475 q = 1) : d357795 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d357795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d357795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42299 q = 1) : d357651 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d357651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42299, d357651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99391 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42256 q = 1) : d357608 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99391 q ha hb
    | true =>
      simp only [d42256, d357608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42300 q = 1) : d357652 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d357652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42300, d357652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42257 q = 1) : d357609 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42257, d357609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42301 q = 1) : d357653 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d357653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42301, d357653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42302 q = 1) : d357654 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d357654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42302, d357654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42476 q = 1) : d357796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42476, d357796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42476, d357796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42477 q = 1) : d357797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d357797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42477, d357797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42378 q = 1) : d357729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
    | true =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42478 q = 1) : d357798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d357798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42478, d357798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42379 q = 1) : d357730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42479 q = 1) : d357799 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d357799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42479, d357799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d42480 q = 1) : d357800 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d357800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42480, d357800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d69 q = 1) : d69 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d42481 q = 1) : d357801 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d357801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42481, d357801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d42482 q = 1) : d357802 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42482, d357802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42482, d357802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro99424 (p : Pattern) (ha : d14 p = 1) (hb : d42488 p = 1) : d357808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42483 q = 1) : d357803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d357803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99423 q ha hb
    | true =>
      simp only [d42483, d357803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42484 q = 1) : d357804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d357804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42484, d357804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42485 q = 1) : d357805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d357805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42485, d357805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d71 q = 1) : d71 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42305 q = 1) : d357657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
    | true =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42306 q = 1) : d357658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42307 q = 1) : d357659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42486 q = 1) : d357806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d357806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d357806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d74 q = 1) : d74 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42308 q = 1) : d357660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d357660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42308, d357660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42487 q = 1) : d357807 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42487, d357807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42487, d357807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42488 q = 1) : d357808 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42488, d357808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42488, d357808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro99425 (p : Pattern) (ha : d14 p = 1) (hb : d42494 p = 1) : d357814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42489 q = 1) : d357809 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42489, d357809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99424 q ha hb
    | true =>
      simp only [d42489, d357809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42490 q = 1) : d357810 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42490, d357810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42490, d357810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42311 q = 1) : d357663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d357663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99400 q ha hb
    | true =>
      simp only [d42311, d357663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42312 q = 1) : d357664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d357664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42312, d357664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42491 q = 1) : d357811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42491, d357811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42491, d357811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42492 q = 1) : d357812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42492, d357812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42492, d357812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42493 q = 1) : d357813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42493, d357813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42493, d357813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42494 q = 1) : d357814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42494, d357814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42494, d357814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99426 (p : Pattern) (ha : d14 p = 1) (hb : d42519 p = 1) : d357820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42311 q = 1) : d357663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d357663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99400 q ha hb
    | true =>
      simp only [d42311, d357663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42312 q = 1) : d357664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d357664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42312, d357664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42516 q = 1) : d357817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42516, d357817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42516, d357817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42517 q = 1) : d357818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42517, d357818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42517, d357818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42518 q = 1) : d357819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42518, d357819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42518, d357819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42519 q = 1) : d357820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42519, d357820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42519, d357820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99427 (p : Pattern) (ha : d14 p = 1) (hb : d309831 p = 1) : d357826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42495 q = 1) : d357815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42495, d357815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99425 q ha hb
    | true =>
      simp only [d42495, d357815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99401 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309827 q = 1) : d357816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d357816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309827, d357816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42520 q = 1) : d357821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42520, d357821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99426 q ha hb
    | true =>
      simp only [d42520, d357821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42521 q = 1) : d357822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42521, d357822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42521, d357822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309828 q = 1) : d357823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d357823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309828, d357823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309829 q = 1) : d357824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d357824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309829, d357824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309830 q = 1) : d357825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d357825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309830, d357825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309831 q = 1) : d357826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d357826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309831, d357826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99428 (p : Pattern) (ha : d14 p = 1) (hb : d309837 p = 1) : d357832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42339 q = 1) : d357691 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42339, d357691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42339, d357691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99404 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42340 q = 1) : d357692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42340, d357692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42340, d357692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42346 q = 1) : d357698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99404 q ha hb
    | true =>
      simp only [d42346, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99405 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42347 q = 1) : d357699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42347, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42348 q = 1) : d357700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42348, d357700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42348, d357700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309815 q = 1) : d357778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d357778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99416 q ha hb
    | true =>
      simp only [d309815, d357778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99421 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d111 q = 1) : d111 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42460 q = 1) : d357780 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42460, d357780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99406 q ha hb
    | true =>
      simp only [d42460, d357780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309816 q = 1) : d357781 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d357781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309816, d357781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d309817 q = 1) : d357782 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d357782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309817, d357782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309818 q = 1) : d357783 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d357783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309818, d357783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309822 q = 1) : d357787 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d357787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309822, d357787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99422 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d407 q = 1) : d407 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309823 q = 1) : d357788 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d357788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309823, d357788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309824 q = 1) : d357789 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d357789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309824, d357789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309825 q = 1) : d357790 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d357790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309825, d357790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d309826 q = 1) : d357791 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d357791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309826, d357791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d309832 q = 1) : d357827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d357827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309832, d357827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99427 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d463 q = 1) : d463 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d309833 q = 1) : d357828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d357828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309833, d357828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d309834 q = 1) : d357829 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d357829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309834, d357829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d309835 q = 1) : d357830 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d357830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309835, d357830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d309836 q = 1) : d357831 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d357831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309836, d357831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14 q = 1) (hb : d309837 q = 1) : d357832 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d357832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309837, d357832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro99429 (p : Pattern) (ha : d14 p = 1) (hb : d309843 p = 1) : d357838 p = 1 := by
  have h0 (q : Pattern) (ha : d14 q = 1) (hb : d99 q = 1) : d99 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309800 q = 1) : d357681 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309800, d357681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309800, d357681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99403 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d309801 q = 1) : d357682 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309801, d357682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309801, d357682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d309802 q = 1) : d357683 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309802, d357683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309802, d357683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309803 q = 1) : d357684 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309803, d357684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309803, d357684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309804 q = 1) : d357685 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d357685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309804, d357685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309838 q = 1) : d357833 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d357833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309838, d357833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99428 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309839 q = 1) : d357834 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d357834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309839, d357834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309840 q = 1) : d357835 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d357835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309840, d357835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d309841 q = 1) : d357836 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d357836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309841, d357836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309842 q = 1) : d357837 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d357837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309842, d357837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309843 q = 1) : d357838 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d357838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309843, d357838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro99430 (p : Pattern) (ha : d14 p = 1) (hb : d42540 p = 1) : d357841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42384 q = 1) : d357735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d357735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99412 q ha hb
    | true =>
      simp only [d42384, d357735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42385 q = 1) : d357736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d357736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42385, d357736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42386 q = 1) : d357737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d357737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42386, d357737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d30 q = 1) : d30 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42262 q = 1) : d357614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
    | true =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42263 q = 1) : d357615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42264 q = 1) : d357616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42387 q = 1) : d357738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d357738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d357738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42538 q = 1) : d357839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d357839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42538, d357839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42539 q = 1) : d357840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42539, d357840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42539, d357840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42540 q = 1) : d357841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42540, d357841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42540, d357841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro99431 (p : Pattern) (ha : d14 p = 1) (hb : d42544 p = 1) : d357845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d30 q = 1) : d30 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42262 q = 1) : d357614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
    | true =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42263 q = 1) : d357615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42264 q = 1) : d357616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42538 q = 1) : d357839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d357839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42538, d357839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42543 q = 1) : d357844 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42543, d357844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42543, d357844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42544 q = 1) : d357845 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42544, d357845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42544, d357845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99432 (p : Pattern) (ha : d14 p = 1) (hb : d42550 p = 1) : d357851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42547 q = 1) : d357848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42548 q = 1) : d357849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42549 q = 1) : d357850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d357850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d357850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42550 q = 1) : d357851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42550, d357851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42550, d357851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99433 (p : Pattern) (ha : d14 p = 1) (hb : d42554 p = 1) : d357855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42551 q = 1) : d357852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42552 q = 1) : d357853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42553 q = 1) : d357854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d357854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d357854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42554 q = 1) : d357855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42554, d357855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42554, d357855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99434 (p : Pattern) (ha : d14 p = 1) (hb : d42560 p = 1) : d357861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42555 q = 1) : d357856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99432 q ha hb
    | true =>
      simp only [d42555, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99433 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42556 q = 1) : d357857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42556, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42557 q = 1) : d357858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42558 q = 1) : d357859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42558, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42559 q = 1) : d357860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42559, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42560 q = 1) : d357861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42560, d357861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42560, d357861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99435 (p : Pattern) (ha : d14 p = 1) (hb : d42563 p = 1) : d357864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42547 q = 1) : d357848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42548 q = 1) : d357849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42549 q = 1) : d357850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d357850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d357850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42563 q = 1) : d357864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42563, d357864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42563, d357864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99436 (p : Pattern) (ha : d14 p = 1) (hb : d42564 p = 1) : d357865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42551 q = 1) : d357852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42552 q = 1) : d357853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42553 q = 1) : d357854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d357854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d357854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42564 q = 1) : d357865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42564, d357865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42564, d357865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99437 (p : Pattern) (ha : d14 p = 1) (hb : d42570 p = 1) : d357871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42555 q = 1) : d357856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99432 q ha hb
    | true =>
      simp only [d42555, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99433 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42556 q = 1) : d357857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42556, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42557 q = 1) : d357858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42558 q = 1) : d357859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42558, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42559 q = 1) : d357860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42559, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42565 q = 1) : d357866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99435 q ha hb
    | true =>
      simp only [d42565, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99436 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42566 q = 1) : d357867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42566, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42567 q = 1) : d357868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42567, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42568 q = 1) : d357869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42568, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42569 q = 1) : d357870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42569, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42570 q = 1) : d357871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42570, d357871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42570, d357871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99438 (p : Pattern) (ha : d14 p = 1) (hb : d42730 p = 1) : d357980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42555 q = 1) : d357856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99432 q ha hb
    | true =>
      simp only [d42555, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99433 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42556 q = 1) : d357857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42556, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42557 q = 1) : d357858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42558 q = 1) : d357859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42558, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42559 q = 1) : d357860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42559, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42725 q = 1) : d357975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d357975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99433 q ha hb
    | true =>
      simp only [d42725, d357975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42726 q = 1) : d357976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d357976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42726, d357976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42727 q = 1) : d357977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d357977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42727, d357977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42728 q = 1) : d357978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d357978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42728, d357978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42729 q = 1) : d357979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d357979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42729, d357979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42730 q = 1) : d357980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42730, d357980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42730, d357980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99439 (p : Pattern) (ha : d14 p = 1) (hb : d42736 p = 1) : d357986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42725 q = 1) : d357975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d357975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99433 q ha hb
    | true =>
      simp only [d42725, d357975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42726 q = 1) : d357976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d357976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42726, d357976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42727 q = 1) : d357977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d357977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42727, d357977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42728 q = 1) : d357978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d357978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42728, d357978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42729 q = 1) : d357979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d357979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42729, d357979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42731 q = 1) : d357981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d357981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99436 q ha hb
    | true =>
      simp only [d42731, d357981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42732 q = 1) : d357982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d357982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42732, d357982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42733 q = 1) : d357983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d357983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42733, d357983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42734 q = 1) : d357984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d357984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42734, d357984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42735 q = 1) : d357985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d357985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42735, d357985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42736 q = 1) : d357986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42736, d357986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42736, d357986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99440 (p : Pattern) (ha : d14 p = 1) (hb : d42745 p = 1) : d357995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42731 q = 1) : d357981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d357981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99436 q ha hb
    | true =>
      simp only [d42731, d357981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42732 q = 1) : d357982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d357982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42732, d357982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42733 q = 1) : d357983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d357983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42733, d357983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42734 q = 1) : d357984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d357984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42734, d357984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42735 q = 1) : d357985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d357985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42735, d357985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42745 q = 1) : d357995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42745, d357995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42745, d357995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99441 (p : Pattern) (ha : d14 p = 1) (hb : d42788 p = 1) : d358038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d71 q = 1) : d71 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42305 q = 1) : d357657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
    | true =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42306 q = 1) : d357658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42307 q = 1) : d357659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42778 q = 1) : d358028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d358028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42778, d358028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42787 q = 1) : d358037 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42787, d358037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42787, d358037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42788 q = 1) : d358038 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42788, d358038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42788, d358038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro99442 (p : Pattern) (ha : d14 p = 1) (hb : d42844 p = 1) : d358061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42789 q = 1) : d358039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d358039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99441 q ha hb
    | true =>
      simp only [d42789, d358039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42790 q = 1) : d358040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d358040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42790, d358040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42841 q = 1) : d358058 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42841, d358058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42841, d358058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42842 q = 1) : d358059 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42842, d358059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42842, d358059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42843 q = 1) : d358060 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42843, d358060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42843, d358060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42844 q = 1) : d358061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42844, d358061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42844, d358061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99443 (p : Pattern) (ha : d14 p = 1) (hb : d42850 p = 1) : d358067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42845 q = 1) : d358062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42845, d358062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99442 q ha hb
    | true =>
      simp only [d42845, d358062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42846 q = 1) : d358063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42846, d358063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42846, d358063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42847 q = 1) : d358064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42847, d358064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42847, d358064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42848 q = 1) : d358065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42848, d358065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42848, d358065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42849 q = 1) : d358066 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42849, d358066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42849, d358066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42850 q = 1) : d358067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42850, d358067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42850, d358067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99444 (p : Pattern) (ha : d14 p = 1) (hb : d42575 p = 1) : d357876 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42547 q = 1) : d357848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42548 q = 1) : d357849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42574 q = 1) : d357875 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d357875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42574, d357875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42575 q = 1) : d357876 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42575, d357876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42575, d357876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99445 (p : Pattern) (ha : d14 p = 1) (hb : d42577 p = 1) : d357878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42551 q = 1) : d357852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42552 q = 1) : d357853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42576 q = 1) : d357877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d357877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42576, d357877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42577 q = 1) : d357878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42577, d357878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42577, d357878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99446 (p : Pattern) (ha : d14 p = 1) (hb : d42584 p = 1) : d357885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42547 q = 1) : d357848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42582 q = 1) : d357883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d357883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42582, d357883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42583 q = 1) : d357884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d357884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d357884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42584 q = 1) : d357885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42584, d357885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42584, d357885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99447 (p : Pattern) (ha : d14 p = 1) (hb : d42587 p = 1) : d357888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42551 q = 1) : d357852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42585 q = 1) : d357886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d357886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42585, d357886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42586 q = 1) : d357887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d357887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d357887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42587 q = 1) : d357888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42587, d357888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42587, d357888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99448 (p : Pattern) (ha : d14 p = 1) (hb : d42594 p = 1) : d357893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d2001 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d1519 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d34366 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42591 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42592 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42246 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42247 q = 1) : d357599 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d357599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42247, d357599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42593 q = 1) : d357892 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42593, d357892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42593, d357892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42594 q = 1) : d357893 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42594, d357893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42594, d357893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro99449 (p : Pattern) (ha : d14 p = 1) (hb : d42601 p = 1) : d357899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d1523 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42246 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42246, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42361 q = 1) : d44996 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42361, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42598 q = 1) : d1085 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42598, d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42598, d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42599 q = 1) : d357897 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42599, d357897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42599, d357897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d16 q = 1) : d16 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42600 q = 1) : d357898 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d357898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42600, d357898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42601 q = 1) : d357899 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42601, d357899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42601, d357899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro99450 (p : Pattern) (ha : d14 p = 1) (hb : d42607 p = 1) : d357905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42595 q = 1) : d357894 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d357894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99448 q ha hb
    | true =>
      simp only [d42595, d357894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42596 q = 1) : d357895 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d357895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d357895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42364 q = 1) : d357715 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99409 q ha hb
    | true =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42365 q = 1) : d357716 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42597 q = 1) : d357896 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d357896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d357896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42602 q = 1) : d357900 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d357900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99449 q ha hb
    | true =>
      simp only [d42602, d357900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42603 q = 1) : d357901 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d357901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d357901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42604 q = 1) : d357902 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d357902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d357902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42605 q = 1) : d357903 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d357903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d357903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42606 q = 1) : d357904 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d357904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d357904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42366 q = 1) : d357717 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42367 q = 1) : d357718 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d357718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42367, d357718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42368 q = 1) : d357719 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d357719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42368, d357719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42607 q = 1) : d357905 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42607, d357905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42607, d357905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro99451 (p : Pattern) (ha : d14 p = 1) (hb : d42612 p = 1) : d357910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42364 q = 1) : d357715 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99409 q ha hb
    | true =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42365 q = 1) : d357716 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42366 q = 1) : d357717 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42367 q = 1) : d357718 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d357718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d357718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42368 q = 1) : d357719 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d357719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42368, d357719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42375 q = 1) : d357726 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d357726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42375, d357726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42376 q = 1) : d357727 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d357727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42376, d357727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42612 q = 1) : d357910 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42612, d357910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42612, d357910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro99452 (p : Pattern) (ha : d14 p = 1) (hb : d42620 p = 1) : d357918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42364 q = 1) : d357715 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99409 q ha hb
    | true =>
      simp only [d42364, d357715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42365 q = 1) : d357716 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d357716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42366 q = 1) : d357717 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d357717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42618 q = 1) : d357916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42618, d357916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42618, d357916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42619 q = 1) : d357917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42619, d357917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42619, d357917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42375 q = 1) : d357726 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d357726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42375, d357726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42376 q = 1) : d357727 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d357727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42376, d357727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42620 q = 1) : d357918 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42620, d357918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42620, d357918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro99453 (p : Pattern) (ha : d14 p = 1) (hb : d42626 p = 1) : d357924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42608 q = 1) : d357906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d357906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99450 q ha hb
    | true =>
      simp only [d42608, d357906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42609 q = 1) : d357907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d357907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d357907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42610 q = 1) : d357908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d357908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42610, d357908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42611 q = 1) : d357909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d357909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d357909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42613 q = 1) : d357911 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d357911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99451 q ha hb
    | true =>
      simp only [d42613, d357911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42614 q = 1) : d357912 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d357912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d357912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42615 q = 1) : d357913 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d357913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42615, d357913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42616 q = 1) : d357914 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d357914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d357914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42617 q = 1) : d357915 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d357915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d357915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42621 q = 1) : d357919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d357919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99452 q ha hb
    | true =>
      simp only [d42621, d357919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42622 q = 1) : d357920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d357920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d357920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42623 q = 1) : d357921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d357921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42623, d357921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42624 q = 1) : d357922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d357922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d357922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42378 q = 1) : d357729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
    | true =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42379 q = 1) : d357730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42380 q = 1) : d357731 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d357731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42380, d357731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42381 q = 1) : d357732 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d357732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42381, d357732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42625 q = 1) : d357923 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42625, d357923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42625, d357923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d42626 q = 1) : d357924 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42626, d357924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42626, d357924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99454 (p : Pattern) (ha : d14 p = 1) (hb : d42630 p = 1) : d357928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42378 q = 1) : d357729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
    | true =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42379 q = 1) : d357730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42380 q = 1) : d357731 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d357731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42380, d357731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42381 q = 1) : d357732 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d357732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42381, d357732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d28 q = 1) : d28 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42382 q = 1) : d357733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d357733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42382, d357733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d29 q = 1) : d29 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42630 q = 1) : d357928 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42630, d357928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42630, d357928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99455 (p : Pattern) (ha : d14 p = 1) (hb : d42636 p = 1) : d357934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42627 q = 1) : d357925 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42627, d357925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99453 q ha hb
    | true =>
      simp only [d42627, d357925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99412 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42628 q = 1) : d357926 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42628, d357926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42628, d357926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42629 q = 1) : d357927 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42629, d357927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42629, d357927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42631 q = 1) : d357929 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42631, d357929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99412 q ha hb
    | true =>
      simp only [d42631, d357929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99454 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42632 q = 1) : d357930 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42632, d357930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42632, d357930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42633 q = 1) : d357931 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42633, d357931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42633, d357931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42634 q = 1) : d357932 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42634, d357932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42634, d357932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42384 q = 1) : d357735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d357735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99412 q ha hb
    | true =>
      simp only [d42384, d357735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42385 q = 1) : d357736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d357736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42385, d357736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42386 q = 1) : d357737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d357737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42386, d357737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d30 q = 1) : d30 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42262 q = 1) : d357614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99392 q ha hb
    | true =>
      simp only [d42262, d357614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42263 q = 1) : d357615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d357615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42264 q = 1) : d357616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d357616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42387 q = 1) : d357738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d357738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42387, d357738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42635 q = 1) : d357933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42635, d357933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42635, d357933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42636 q = 1) : d357934 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42636, d357934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42636, d357934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro99456 (p : Pattern) (ha : d14 p = 1) (hb : d42642 p = 1) : d357940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42637 q = 1) : d357935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d357935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99455 q ha hb
    | true =>
      simp only [d42637, d357935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42638 q = 1) : d357936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d357936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42638, d357936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42639 q = 1) : d357937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d357937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d357937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42640 q = 1) : d357938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d357938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d357938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42641 q = 1) : d357939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d357939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d357939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42642 q = 1) : d357940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42642, d357940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42642, d357940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99457 (p : Pattern) (ha : d14 p = 1) (hb : d42693 p = 1) : d357946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42690 q = 1) : d357943 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d357943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d357943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42691 q = 1) : d357944 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d357944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d357944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42692 q = 1) : d357945 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d357945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d357945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42693 q = 1) : d357946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42693, d357946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42693, d357946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99458 (p : Pattern) (ha : d14 p = 1) (hb : d309848 p = 1) : d357952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42578 q = 1) : d357879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d357879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99444 q ha hb
    | true =>
      simp only [d42578, d357879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99445 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42579 q = 1) : d357880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d357880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42579, d357880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42580 q = 1) : d357881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d357881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d357881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42581 q = 1) : d357882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d357882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42581, d357882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42588 q = 1) : d357889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d357889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99446 q ha hb
    | true =>
      simp only [d42588, d357889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99447 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42589 q = 1) : d357890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d357890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42589, d357890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42590 q = 1) : d357891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d357891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d357891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42643 q = 1) : d357941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d357941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99456 q ha hb
    | true =>
      simp only [d42643, d357941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99432 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309844 q = 1) : d357942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d357942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309844, d357942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42694 q = 1) : d357947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d357947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99457 q ha hb
    | true =>
      simp only [d42694, d357947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42695 q = 1) : d357948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d357948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d357948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309845 q = 1) : d357949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d357949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d357949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309846 q = 1) : d357950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d357950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309846, d357950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309847 q = 1) : d357951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d357951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309847, d357951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309848 q = 1) : d357952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d357952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309848, d357952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99459 (p : Pattern) (ha : d14 p = 1) (hb : d42700 p = 1) : d357953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42547 q = 1) : d357848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42548 q = 1) : d357849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d357849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42574 q = 1) : d357875 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d357875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42574, d357875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42700 q = 1) : d357953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42700, d357953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42700, d357953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99460 (p : Pattern) (ha : d14 p = 1) (hb : d42701 p = 1) : d357954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42551 q = 1) : d357852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42552 q = 1) : d357853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d357853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42576 q = 1) : d357877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d357877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42576, d357877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42701 q = 1) : d357954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42701, d357954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42701, d357954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99461 (p : Pattern) (ha : d14 p = 1) (hb : d42706 p = 1) : d357959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42547 q = 1) : d357848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d357848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42582 q = 1) : d357883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d357883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42582, d357883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42583 q = 1) : d357884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d357884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d357884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42706 q = 1) : d357959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42706, d357959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42706, d357959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99462 (p : Pattern) (ha : d14 p = 1) (hb : d42707 p = 1) : d357960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42545 q = 1) : d357846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99431 q ha hb
    | true =>
      simp only [d42545, d357846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42546 q = 1) : d357847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d357847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42551 q = 1) : d357852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d357852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42585 q = 1) : d357886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d357886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42585, d357886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42586 q = 1) : d357887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d357887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d357887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42707 q = 1) : d357960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42707, d357960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42707, d357960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99463 (p : Pattern) (ha : d14 p = 1) (hb : d42711 p = 1) : d357964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42637 q = 1) : d357935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d357935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99455 q ha hb
    | true =>
      simp only [d42637, d357935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42638 q = 1) : d357936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d357936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42638, d357936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42639 q = 1) : d357937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d357937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d357937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42640 q = 1) : d357938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d357938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d357938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42641 q = 1) : d357939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d357939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d357939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42711 q = 1) : d357964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42711, d357964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42711, d357964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99464 (p : Pattern) (ha : d14 p = 1) (hb : d42717 p = 1) : d357967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42541 q = 1) : d357842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99430 q ha hb
    | true =>
      simp only [d42541, d357842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42542 q = 1) : d357843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d357843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42690 q = 1) : d357943 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d357943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d357943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42691 q = 1) : d357944 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d357944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d357944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42692 q = 1) : d357945 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d357945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d357945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42717 q = 1) : d357967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42717, d357967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42717, d357967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99465 (p : Pattern) (ha : d14 p = 1) (hb : d309853 p = 1) : d357973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42578 q = 1) : d357879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d357879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99444 q ha hb
    | true =>
      simp only [d42578, d357879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99445 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42579 q = 1) : d357880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d357880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42579, d357880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42580 q = 1) : d357881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d357881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d357881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42581 q = 1) : d357882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d357882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42581, d357882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42588 q = 1) : d357889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d357889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99446 q ha hb
    | true =>
      simp only [d42588, d357889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99447 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42589 q = 1) : d357890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d357890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42589, d357890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42590 q = 1) : d357891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d357891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d357891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42643 q = 1) : d357941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d357941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99456 q ha hb
    | true =>
      simp only [d42643, d357941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99432 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309844 q = 1) : d357942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d357942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309844, d357942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42694 q = 1) : d357947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d357947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99457 q ha hb
    | true =>
      simp only [d42694, d357947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42695 q = 1) : d357948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d357948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d357948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d309845 q = 1) : d357949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d357949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d357949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309846 q = 1) : d357950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d357950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309846, d357950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309847 q = 1) : d357951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d357951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309847, d357951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42702 q = 1) : d357955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42702, d357955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99459 q ha hb
    | true =>
      simp only [d42702, d357955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99460 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42703 q = 1) : d357956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42703, d357956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42703, d357956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42704 q = 1) : d357957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42704, d357957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42704, d357957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42705 q = 1) : d357958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42705, d357958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42705, d357958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d42708 q = 1) : d357961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42708, d357961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99461 q ha hb
    | true =>
      simp only [d42708, d357961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99462 q ha hb
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d42709 q = 1) : d357962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42709, d357962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42709, d357962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d42710 q = 1) : d357963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42710, d357963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42710, d357963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d42712 q = 1) : d357965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d357965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99463 q ha hb
    | true =>
      simp only [d42712, d357965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99435 q ha hb
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d309849 q = 1) : d357966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d357966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309849, d357966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14 q = 1) (hb : d42718 q = 1) : d357968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d357968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99464 q ha hb
    | true =>
      simp only [d42718, d357968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d14 q = 1) (hb : d42719 q = 1) : d357969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d357969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42719, d357969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d14 q = 1) (hb : d309850 q = 1) : d357970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d357970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309850, d357970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d14 q = 1) (hb : d309851 q = 1) : d357971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d357971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309851, d357971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d14 q = 1) (hb : d309852 q = 1) : d357972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d357972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309852, d357972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d14 q = 1) (hb : d309853 q = 1) : d357973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d357973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309853, d357973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro99466 (p : Pattern) (ha : d14 p = 1) (hb : d309860 p = 1) : d357993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42712 q = 1) : d357965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d357965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99463 q ha hb
    | true =>
      simp only [d42712, d357965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99435 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309849 q = 1) : d357966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d357966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309849, d357966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42718 q = 1) : d357968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d357968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99464 q ha hb
    | true =>
      simp only [d42718, d357968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42719 q = 1) : d357969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d357969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42719, d357969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309850 q = 1) : d357970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d357970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309850, d357970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309858 q = 1) : d357991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d357991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309858, d357991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309859 q = 1) : d357992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d357992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309859, d357992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309860 q = 1) : d357993 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d357993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309860, d357993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99467 (p : Pattern) (ha : d14 p = 1) (hb : d42765 p = 1) : d358015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42751 q = 1) : d358001 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d358001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42751, d358001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99450 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42608 q = 1) : d357906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d357906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99450 q ha hb
    | true =>
      simp only [d42608, d357906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42752 q = 1) : d358002 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d358002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d358002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42609 q = 1) : d357907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d357907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d357907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42753 q = 1) : d358003 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d358003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d358003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42754 q = 1) : d358004 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d358004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d358004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42755 q = 1) : d358005 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d358005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42755, d358005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99451 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42613 q = 1) : d357911 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d357911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99451 q ha hb
    | true =>
      simp only [d42613, d357911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42756 q = 1) : d358006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d358006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d358006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42614 q = 1) : d357912 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d357912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d357912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42757 q = 1) : d358007 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d358007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d358007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42758 q = 1) : d358008 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d358008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d358008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42759 q = 1) : d358009 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d358009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d358009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42760 q = 1) : d358010 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d358010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42760, d358010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99452 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42621 q = 1) : d357919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d357919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99452 q ha hb
    | true =>
      simp only [d42621, d357919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42761 q = 1) : d358011 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d358011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d358011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42622 q = 1) : d357920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d357920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d357920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42762 q = 1) : d358012 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d358012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d358012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d42763 q = 1) : d358013 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d358013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d358013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d42477 q = 1) : d357797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d357797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42477, d357797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d42378 q = 1) : d357729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
    | true =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d42478 q = 1) : d357798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d357798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42478, d357798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d42379 q = 1) : d357730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14 q = 1) (hb : d42479 q = 1) : d357799 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d357799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42479, d357799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d14 q = 1) (hb : d42480 q = 1) : d357800 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d357800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42480, d357800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d14 q = 1) (hb : d42764 q = 1) : d358014 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42764, d358014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42764, d358014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d14 q = 1) (hb : d42765 q = 1) : d358015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42765, d358015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42765, d358015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro99468 (p : Pattern) (ha : d14 p = 1) (hb : d42769 p = 1) : d358019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42477 q = 1) : d357797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d357797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42477, d357797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42378 q = 1) : d357729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99411 q ha hb
    | true =>
      simp only [d42378, d357729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42478 q = 1) : d357798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d357798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42478, d357798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42379 q = 1) : d357730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42379, d357730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42479 q = 1) : d357799 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d357799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42479, d357799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42480 q = 1) : d357800 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d357800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42480, d357800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d69 q = 1) : d69 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42481 q = 1) : d357801 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d357801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42481, d357801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d70 q = 1) : d70 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42769 q = 1) : d358019 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42769, d358019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42769, d358019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro99469 (p : Pattern) (ha : d14 p = 1) (hb : d42775 p = 1) : d358025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42766 q = 1) : d358016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42766, d358016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99467 q ha hb
    | true =>
      simp only [d42766, d358016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99423 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42767 q = 1) : d358017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42767, d358017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42767, d358017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42768 q = 1) : d358018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42768, d358018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42768, d358018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42770 q = 1) : d358020 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42770, d358020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99423 q ha hb
    | true =>
      simp only [d42770, d358020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99468 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42771 q = 1) : d358021 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42771, d358021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42771, d358021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42772 q = 1) : d358022 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42772, d358022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42772, d358022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42773 q = 1) : d358023 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42773, d358023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42773, d358023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42483 q = 1) : d357803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d357803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99423 q ha hb
    | true =>
      simp only [d42483, d357803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42484 q = 1) : d357804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d357804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42484, d357804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42485 q = 1) : d357805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d357805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42485, d357805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d71 q = 1) : d71 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42305 q = 1) : d357657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
    | true =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42306 q = 1) : d357658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42307 q = 1) : d357659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42486 q = 1) : d357806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d357806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42486, d357806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42774 q = 1) : d358024 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42774, d358024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42774, d358024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42775 q = 1) : d358025 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42775, d358025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42775, d358025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro99470 (p : Pattern) (ha : d14 p = 1) (hb : d42780 p = 1) : d358030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42483 q = 1) : d357803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d357803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99423 q ha hb
    | true =>
      simp only [d42483, d357803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42484 q = 1) : d357804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d357804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42484, d357804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42485 q = 1) : d357805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d357805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42485, d357805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d71 q = 1) : d71 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42305 q = 1) : d357657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99399 q ha hb
    | true =>
      simp only [d42305, d357657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42306 q = 1) : d357658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d357658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42307 q = 1) : d357659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d357659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42486 q = 1) : d357806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d357806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d357806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42778 q = 1) : d358028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d358028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42778, d358028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42779 q = 1) : d358029 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42779, d358029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42779, d358029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42780 q = 1) : d358030 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42780, d358030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42780, d358030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro99471 (p : Pattern) (ha : d14 p = 1) (hb : d42786 p = 1) : d358036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42776 q = 1) : d358026 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42776, d358026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99469 q ha hb
    | true =>
      simp only [d42776, d358026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42777 q = 1) : d358027 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42777, d358027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42777, d358027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42781 q = 1) : d358031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d358031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99470 q ha hb
    | true =>
      simp only [d42781, d358031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42782 q = 1) : d358032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d358032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42782, d358032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42783 q = 1) : d358033 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42783, d358033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42783, d358033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42784 q = 1) : d358034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42784, d358034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42784, d358034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42785 q = 1) : d358035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42785, d358035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42785, d358035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42786 q = 1) : d358036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42786, d358036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42786, d358036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99472 (p : Pattern) (ha : d14 p = 1) (hb : d42794 p = 1) : d358044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42781 q = 1) : d358031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d358031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99470 q ha hb
    | true =>
      simp only [d42781, d358031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42782 q = 1) : d358032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d358032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42782, d358032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42789 q = 1) : d358039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d358039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99441 q ha hb
    | true =>
      simp only [d42789, d358039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42790 q = 1) : d358040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d358040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42790, d358040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42791 q = 1) : d358041 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42791, d358041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42791, d358041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42792 q = 1) : d358042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42792, d358042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42792, d358042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42793 q = 1) : d358043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42793, d358043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42793, d358043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42794 q = 1) : d358044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42794, d358044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42794, d358044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99473 (p : Pattern) (ha : d14 p = 1) (hb : d42833 p = 1) : d358050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42781 q = 1) : d358031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d358031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99470 q ha hb
    | true =>
      simp only [d42781, d358031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42782 q = 1) : d358032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d358032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42782, d358032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42830 q = 1) : d358047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42830, d358047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42830, d358047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42831 q = 1) : d358048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42831, d358048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42831, d358048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42832 q = 1) : d358049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42832, d358049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42832, d358049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42833 q = 1) : d358050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42833, d358050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42833, d358050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99474 (p : Pattern) (ha : d14 p = 1) (hb : d309870 p = 1) : d358056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42795 q = 1) : d358045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42795, d358045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99471 q ha hb
    | true =>
      simp only [d42795, d358045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99472 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309866 q = 1) : d358046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d358046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309866, d358046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42834 q = 1) : d358051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42834, d358051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99473 q ha hb
    | true =>
      simp only [d42834, d358051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42835 q = 1) : d358052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42835, d358052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42835, d358052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309867 q = 1) : d358053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d358053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309867, d358053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309868 q = 1) : d358054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d358054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309868, d358054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309869 q = 1) : d358055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d358055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309869, d358055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309870 q = 1) : d358056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d358056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309870, d358056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99475 (p : Pattern) (ha : d14 p = 1) (hb : d309876 p = 1) : d358073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42561 q = 1) : d357862 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42561, d357862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42561, d357862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99434 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42562 q = 1) : d357863 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42562, d357863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42562, d357863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42571 q = 1) : d357872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99434 q ha hb
    | true =>
      simp only [d42571, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99437 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42572 q = 1) : d357873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42572, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42573 q = 1) : d357874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42573, d357874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42573, d357874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309854 q = 1) : d357974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d357974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99458 q ha hb
    | true =>
      simp only [d309854, d357974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99465 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42737 q = 1) : d357987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42737, d357987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99438 q ha hb
    | true =>
      simp only [d42737, d357987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99439 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309855 q = 1) : d357988 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d357988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309855, d357988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309856 q = 1) : d357989 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d357989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309856, d357989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d309857 q = 1) : d357990 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d357990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309857, d357990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d309861 q = 1) : d357994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d357994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309861, d357994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99466 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42746 q = 1) : d357996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42746, d357996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42746, d357996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99440 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d309862 q = 1) : d357997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d357997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309862, d357997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d309863 q = 1) : d357998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d357998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309863, d357998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d309864 q = 1) : d357999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d357999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309864, d357999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d309865 q = 1) : d358000 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d358000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309865, d358000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d309871 q = 1) : d358057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d358057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309871, d358057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99474 q ha hb
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42851 q = 1) : d358068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42851, d358068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42851, d358068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99443 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d309872 q = 1) : d358069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d358069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309872, d358069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14 q = 1) (hb : d309873 q = 1) : d358070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d358070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309873, d358070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d14 q = 1) (hb : d309874 q = 1) : d358071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d358071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309874, d358071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d14 q = 1) (hb : d309875 q = 1) : d358072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d358072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309875, d358072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d14 q = 1) (hb : d309876 q = 1) : d358073 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d358073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309876, d358073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro99476 (p : Pattern) (ha : d14 p = 1) (hb : d309882 p = 1) : d358079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d309877 q = 1) : d358074 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d358074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309877, d358074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99475 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d309878 q = 1) : d358075 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d358075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309878, d358075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d309879 q = 1) : d358076 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d358076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309879, d358076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d309880 q = 1) : d358077 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d358077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309880, d358077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d309881 q = 1) : d358078 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d358078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309881, d358078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d309882 q = 1) : d358079 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d358079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309882, d358079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99477 (p : Pattern) (ha : d14 p = 1) (hb : d42864 p = 1) : d358081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42250 q = 1) : d357602 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99390 q ha hb
    | true =>
      simp only [d42250, d357602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42251 q = 1) : d357603 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d357603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42252 q = 1) : d357604 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d357604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d21 q = 1) : d21 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42253 q = 1) : d357605 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d357605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42253, d357605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42254 q = 1) : d357606 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d357606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42254, d357606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42864 q = 1) : d358081 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42864, d358081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42864, d358081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99478 (p : Pattern) (ha : d14 p = 1) (hb : d42870 p = 1) : d358087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42608 q = 1) : d357906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d357906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99450 q ha hb
    | true =>
      simp only [d42608, d357906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42609 q = 1) : d357907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d357907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d357907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42610 q = 1) : d357908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d357908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42610, d357908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42611 q = 1) : d357909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d357909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d357909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42613 q = 1) : d357911 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d357911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99451 q ha hb
    | true =>
      simp only [d42613, d357911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42614 q = 1) : d357912 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d357912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d357912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42615 q = 1) : d357913 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d357913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42615, d357913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42616 q = 1) : d357914 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d357914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d357914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42617 q = 1) : d357915 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d357915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d357915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42621 q = 1) : d357919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d357919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99452 q ha hb
    | true =>
      simp only [d42621, d357919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42622 q = 1) : d357920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d357920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d357920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d42623 q = 1) : d357921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d357921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42623, d357921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d42624 q = 1) : d357922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d357922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d357922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d42865 q = 1) : d358082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
    | true =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d42866 q = 1) : d358083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d42867 q = 1) : d358084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d358084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d358084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d42868 q = 1) : d358085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d358085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42868, d358085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d14 q = 1) (hb : d42869 q = 1) : d358086 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d358086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42869, d358086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14 q = 1) (hb : d42870 q = 1) : d358087 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42870, d358087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42870, d358087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro99479 (p : Pattern) (ha : d14 p = 1) (hb : d42873 p = 1) : d358090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42370 q = 1) : d357721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99410 q ha hb
    | true =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42371 q = 1) : d357722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42372 q = 1) : d357723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d357723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42372, d357723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42373 q = 1) : d357724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d357724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d357724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42865 q = 1) : d358082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
    | true =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42866 q = 1) : d358083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42867 q = 1) : d358084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d358084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d358084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42868 q = 1) : d358085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d358085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d358085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42871 q = 1) : d358088 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42871, d358088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42871, d358088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42872 q = 1) : d358089 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d358089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d358089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42873 q = 1) : d358090 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42873, d358090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42873, d358090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99480 (p : Pattern) (ha : d14 p = 1) (hb : d42877 p = 1) : d358094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42865 q = 1) : d358082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
    | true =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42866 q = 1) : d358083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42867 q = 1) : d358084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d358084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d358084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42868 q = 1) : d358085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d358085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42868, d358085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42872 q = 1) : d358089 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d358089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42872, d358089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42877 q = 1) : d358094 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42877, d358094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42877, d358094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99481 (p : Pattern) (ha : d14 p = 1) (hb : d42884 p = 1) : d358101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42874 q = 1) : d358091 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d358091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99478 q ha hb
    | true =>
      simp only [d42874, d358091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99479 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42875 q = 1) : d358092 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d358092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42875, d358092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42876 q = 1) : d358093 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d358093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42876, d358093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42878 q = 1) : d358095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d358095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99479 q ha hb
    | true =>
      simp only [d42878, d358095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99480 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42879 q = 1) : d358096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d358096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42879, d358096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42880 q = 1) : d358097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d358097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42880, d358097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42881 q = 1) : d358098 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d358098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42881, d358098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42882 q = 1) : d358099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d358099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42882, d358099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42883 q = 1) : d358100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42883, d358100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42883, d358100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42884 q = 1) : d358101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42884, d358101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42884, d358101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro99482 (p : Pattern) (ha : d14 p = 1) (hb : d42888 p = 1) : d358105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42878 q = 1) : d358095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d358095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99479 q ha hb
    | true =>
      simp only [d42878, d358095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99480 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42879 q = 1) : d358096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d358096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42879, d358096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42880 q = 1) : d358097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d358097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42880, d358097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42882 q = 1) : d358099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d358099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42882, d358099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42887 q = 1) : d358104 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42887, d358104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42887, d358104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42888 q = 1) : d358105 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42888, d358105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42888, d358105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99483 (p : Pattern) (ha : d14 p = 1) (hb : d42894 p = 1) : d358111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42885 q = 1) : d358102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99481 q ha hb
    | true =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42886 q = 1) : d358103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42891 q = 1) : d358108 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42892 q = 1) : d358109 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d358109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d358109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42893 q = 1) : d358110 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d358110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d358110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42894 q = 1) : d358111 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42894, d358111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42894, d358111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99484 (p : Pattern) (ha : d14 p = 1) (hb : d42898 p = 1) : d358115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42895 q = 1) : d358112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d358112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d358112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42896 q = 1) : d358113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d358113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d358113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42897 q = 1) : d358114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d358114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d358114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42898 q = 1) : d358115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42898, d358115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42898, d358115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99485 (p : Pattern) (ha : d14 p = 1) (hb : d42904 p = 1) : d358121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42899 q = 1) : d358116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99483 q ha hb
    | true =>
      simp only [d42899, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99484 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42900 q = 1) : d358117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42900, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42901 q = 1) : d358118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42902 q = 1) : d358119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42902, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42903 q = 1) : d358120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42903, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42904 q = 1) : d358121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42904, d358121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42904, d358121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99486 (p : Pattern) (ha : d14 p = 1) (hb : d42907 p = 1) : d358124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42885 q = 1) : d358102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99481 q ha hb
    | true =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42886 q = 1) : d358103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42891 q = 1) : d358108 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42892 q = 1) : d358109 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d358109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d358109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42893 q = 1) : d358110 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d358110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d358110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42907 q = 1) : d358124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42907, d358124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42907, d358124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99487 (p : Pattern) (ha : d14 p = 1) (hb : d42908 p = 1) : d358125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42895 q = 1) : d358112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d358112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d358112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42896 q = 1) : d358113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d358113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d358113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42897 q = 1) : d358114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d358114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d358114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42908 q = 1) : d358125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42908, d358125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42908, d358125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99488 (p : Pattern) (ha : d14 p = 1) (hb : d42914 p = 1) : d358131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42899 q = 1) : d358116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99483 q ha hb
    | true =>
      simp only [d42899, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99484 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42900 q = 1) : d358117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42900, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42901 q = 1) : d358118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42902 q = 1) : d358119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42902, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42903 q = 1) : d358120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42903, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42909 q = 1) : d358126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99486 q ha hb
    | true =>
      simp only [d42909, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99487 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42910 q = 1) : d358127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42910, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42911 q = 1) : d358128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42911, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d42912 q = 1) : d358129 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42912, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42913 q = 1) : d358130 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42913, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d42914 q = 1) : d358131 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42914, d358131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42914, d358131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99489 (p : Pattern) (ha : d14 p = 1) (hb : d43111 p = 1) : d358245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42899 q = 1) : d358116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99483 q ha hb
    | true =>
      simp only [d42899, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99484 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42900 q = 1) : d358117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42900, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42901 q = 1) : d358118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42902 q = 1) : d358119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42902, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42903 q = 1) : d358120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42903, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43106 q = 1) : d358240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d358240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99484 q ha hb
    | true =>
      simp only [d43106, d358240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d43107 q = 1) : d358241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d358241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43107, d358241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d43108 q = 1) : d358242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d358242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43108, d358242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d43109 q = 1) : d358243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d358243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43109, d358243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d43110 q = 1) : d358244 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d358244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43110, d358244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d43111 q = 1) : d358245 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43111, d358245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43111, d358245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99490 (p : Pattern) (ha : d14 p = 1) (hb : d43117 p = 1) : d358251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d43106 q = 1) : d358240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d358240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99484 q ha hb
    | true =>
      simp only [d43106, d358240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d43107 q = 1) : d358241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d358241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43107, d358241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d43108 q = 1) : d358242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d358242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43108, d358242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d43109 q = 1) : d358243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d358243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43109, d358243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d43110 q = 1) : d358244 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d358244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43110, d358244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43112 q = 1) : d358246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d358246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99487 q ha hb
    | true =>
      simp only [d43112, d358246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d43113 q = 1) : d358247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d358247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43113, d358247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d43114 q = 1) : d358248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d358248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43114, d358248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d43115 q = 1) : d358249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d358249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43115, d358249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d43116 q = 1) : d358250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d358250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43116, d358250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d43117 q = 1) : d358251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43117, d358251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43117, d358251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro99491 (p : Pattern) (ha : d14 p = 1) (hb : d43126 p = 1) : d358260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d43112 q = 1) : d358246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d358246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99487 q ha hb
    | true =>
      simp only [d43112, d358246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d43113 q = 1) : d358247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d358247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43113, d358247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d43114 q = 1) : d358248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d358248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43114, d358248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d43115 q = 1) : d358249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d358249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43115, d358249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d43116 q = 1) : d358250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d358250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43116, d358250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43126 q = 1) : d358260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43126, d358260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43126, d358260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99492 (p : Pattern) (ha : d14 p = 1) (hb : d43163 p = 1) : d358297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42472 q = 1) : d357792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d357792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42472, d357792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99410 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42370 q = 1) : d357721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99410 q ha hb
    | true =>
      simp only [d42370, d357721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42473 q = 1) : d357793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d357793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d357793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42371 q = 1) : d357722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d357722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42474 q = 1) : d357794 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d357794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d357794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42475 q = 1) : d357795 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d357795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d357795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d43147 q = 1) : d358281 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d358281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43147, d358281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42865 q = 1) : d358082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
    | true =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d43148 q = 1) : d358282 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d358282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d358282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d42866 q = 1) : d358083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d43149 q = 1) : d358283 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d358283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d358283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d43150 q = 1) : d358284 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d358284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d358284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d43162 q = 1) : d358296 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43162, d358296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43162, d358296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d43156 q = 1) : d358290 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d358290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d358290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d43163 q = 1) : d358297 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43163, d358297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43163, d358297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro99493 (p : Pattern) (ha : d14 p = 1) (hb : d43167 p = 1) : d358301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d43147 q = 1) : d358281 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d358281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43147, d358281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42865 q = 1) : d358082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99477 q ha hb
    | true =>
      simp only [d42865, d358082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d43148 q = 1) : d358282 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d358282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43148, d358282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42866 q = 1) : d358083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42866, d358083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d43149 q = 1) : d358283 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d358283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43149, d358283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43150 q = 1) : d358284 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d358284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43150, d358284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d43156 q = 1) : d358290 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d358290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43156, d358290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d43167 q = 1) : d358301 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43167, d358301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43167, d358301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro99494 (p : Pattern) (ha : d14 p = 1) (hb : d43186 p = 1) : d358320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d43168 q = 1) : d358302 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d358302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99492 q ha hb
    | true =>
      simp only [d43168, d358302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99493 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d43169 q = 1) : d358303 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d358303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43169, d358303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d43170 q = 1) : d358304 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d358304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43170, d358304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d43176 q = 1) : d358310 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d358310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43176, d358310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d43185 q = 1) : d358319 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43185, d358319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43185, d358319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43186 q = 1) : d358320 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43186, d358320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43186, d358320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99495 (p : Pattern) (ha : d14 p = 1) (hb : d43257 p = 1) : d358343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d43187 q = 1) : d358321 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d358321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99494 q ha hb
    | true =>
      simp only [d43187, d358321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d43188 q = 1) : d358322 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d358322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43188, d358322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d43254 q = 1) : d358340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43254, d358340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43254, d358340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d43255 q = 1) : d358341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43255, d358341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43255, d358341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d43256 q = 1) : d358342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43256, d358342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43256, d358342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43257 q = 1) : d358343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43257, d358343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43257, d358343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro99496 (p : Pattern) (ha : d14 p = 1) (hb : d43263 p = 1) : d358349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d43258 q = 1) : d358344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43258, d358344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99495 q ha hb
    | true =>
      simp only [d43258, d358344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d43259 q = 1) : d358345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43259, d358345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43259, d358345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d43260 q = 1) : d358346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43260, d358346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43260, d358346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d43261 q = 1) : d358347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43261, d358347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43261, d358347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d43262 q = 1) : d358348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43262, d358348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43262, d358348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d43263 q = 1) : d358349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43263, d358349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43263, d358349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99497 (p : Pattern) (ha : d14 p = 1) (hb : d42919 p = 1) : d358136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42885 q = 1) : d358102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99481 q ha hb
    | true =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42886 q = 1) : d358103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42891 q = 1) : d358108 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42892 q = 1) : d358109 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d358109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d358109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42918 q = 1) : d358135 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d358135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42918, d358135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42919 q = 1) : d358136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42919, d358136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42919, d358136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro99498 (p : Pattern) (ha : d14 p = 1) (hb : d42921 p = 1) : d358138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42895 q = 1) : d358112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d358112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d358112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42896 q = 1) : d358113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d358113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d358113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42920 q = 1) : d358137 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d358137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42920, d358137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42921 q = 1) : d358138 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42921, d358138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42921, d358138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro99499 (p : Pattern) (ha : d14 p = 1) (hb : d42928 p = 1) : d358145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d42885 q = 1) : d358102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99481 q ha hb
    | true =>
      simp only [d42885, d358102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d42886 q = 1) : d358103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d358103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d42889 q = 1) : d358106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99482 q ha hb
    | true =>
      simp only [d42889, d358106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d42890 q = 1) : d358107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d358107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d42891 q = 1) : d358108 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d358108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d42926 q = 1) : d358143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d358143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42926, d358143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d42927 q = 1) : d358144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d358144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d358144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d42928 q = 1) : d358145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42928, d358145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42928, d358145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
