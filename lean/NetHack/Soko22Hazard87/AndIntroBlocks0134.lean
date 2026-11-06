import NetHack.Soko22Hazard87.AndIntroBlocks0133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro33500 (p : Pattern) (ha : d127663 p = 1) (hb : d162803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127654 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127654, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33498 q ha hb
    | true =>
      simp only [d127654, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127655 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127655, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127655, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127587 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33483 q ha hb
    | true =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127588 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127660 q = 1) (hb : d162800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127660, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127660, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127661 q = 1) (hb : d162801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127661, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127661, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127662 q = 1) (hb : d162802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127662, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127662, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127663 q = 1) (hb : d162803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127663, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127663, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33501 (p : Pattern) (ha : d127671 p = 1) (hb : d162728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127570 q = 1) (hb : d162716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127570, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33479 q ha hb
    | true =>
      simp only [d127570, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33481 q ha hb
  have h2 (q : Pattern) (ha : d127571 q = 1) (hb : d162717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127571, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127571, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127572 q = 1) (hb : d162718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127572, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127572, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127573 q = 1) (hb : d162719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127573, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33481 q ha hb
    | true =>
      simp only [d127573, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22315 q hb ha
  have h5 (q : Pattern) (ha : d127574 q = 1) (hb : d162720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127574, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127574, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127575 q = 1) (hb : d162721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127575, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127575, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127576 q = 1) (hb : d162722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127576, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127576, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127666 q = 1) (hb : d162723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127666, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33481 q ha hb
    | true =>
      simp only [d127666, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18682 q hb ha
  have h9 (q : Pattern) (ha : d127667 q = 1) (hb : d162724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127667, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127667, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127668 q = 1) (hb : d162725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127668, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127668, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127669 q = 1) (hb : d162726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127669, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127669, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127670 q = 1) (hb : d162727 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127670, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127670, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127671 q = 1) (hb : d162728 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127671, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127671, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33502 (p : Pattern) (ha : d127677 p = 1) (hb : d162809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127672 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127672, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33501 q ha hb
    | true =>
      simp only [d127672, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127673 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127673, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127673, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127674 q = 1) (hb : d162806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127674, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127674, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127675 q = 1) (hb : d162807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127675, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127675, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127676 q = 1) (hb : d162808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127676, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127676, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127677 q = 1) (hb : d162809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127677, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127677, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33503 (p : Pattern) (ha : d127683 p = 1) (hb : d162815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127620 q = 1) (hb : d162766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127620, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33490 q ha hb
    | true =>
      simp only [d127620, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33491 q ha hb
  have h2 (q : Pattern) (ha : d127621 q = 1) (hb : d162767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127621, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127621, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127622 q = 1) (hb : d162768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127622, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127622, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127623 q = 1) (hb : d162769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127623, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127623, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127630 q = 1) (hb : d162776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127630, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33492 q ha hb
    | true =>
      simp only [d127630, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33493 q ha hb
  have h6 (q : Pattern) (ha : d127631 q = 1) (hb : d162777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127631, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127631, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127632 q = 1) (hb : d162778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127632, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127632, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127664 q = 1) (hb : d162804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127664, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33499 q ha hb
    | true =>
      simp only [d127664, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33500 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d127665 q = 1) (hb : d162805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127665, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127665, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d127678 q = 1) (hb : d162810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127678, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33502 q ha hb
    | true =>
      simp only [d127678, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127679 q = 1) (hb : d162811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127679, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127679, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127680 q = 1) (hb : d162812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127680, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127680, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127681 q = 1) (hb : d162813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127681, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127681, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127682 q = 1) (hb : d162814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127682, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127682, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d127683 q = 1) (hb : d162815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127683, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127683, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro33504 (p : Pattern) (ha : d127684 p = 1) (hb : d162816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127583 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127583, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33482 q ha hb
    | true =>
      simp only [d127583, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127584 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127584, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127584, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127587 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33483 q ha hb
    | true =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127588 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127589 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127589, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127589, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127590 q = 1) (hb : d162736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127590, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127590, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127616 q = 1) (hb : d162762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127616, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127616, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127684 q = 1) (hb : d162816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127684, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127684, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33505 (p : Pattern) (ha : d127685 p = 1) (hb : d162817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127587 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33483 q ha hb
    | true =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127588 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127593 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127593, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127593, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127594 q = 1) (hb : d162740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127594, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127594, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127618 q = 1) (hb : d162764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127618, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127618, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127685 q = 1) (hb : d162817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127685, d162817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127685, d162817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33506 (p : Pattern) (ha : d127690 p = 1) (hb : d162822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127583 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127583, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33482 q ha hb
    | true =>
      simp only [d127583, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127584 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127584, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127584, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127587 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33483 q ha hb
    | true =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127588 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127589 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127589, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127589, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127624 q = 1) (hb : d162770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127624, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127624, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127625 q = 1) (hb : d162771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127625, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127625, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127690 q = 1) (hb : d162822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127690, d162822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127690, d162822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33507 (p : Pattern) (ha : d127691 p = 1) (hb : d162823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127587 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33483 q ha hb
    | true =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127588 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127593 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127593, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127593, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127627 q = 1) (hb : d162773 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127627, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127627, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127628 q = 1) (hb : d162774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127628, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127628, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127691 q = 1) (hb : d162823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127691, d162823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127691, d162823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33508 (p : Pattern) (ha : d127695 p = 1) (hb : d162827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127649 q = 1) (hb : d162789 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127649, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33497 q ha hb
    | true =>
      simp only [d127649, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127650 q = 1) (hb : d162790 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127650, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127650, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127654 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127654, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33498 q ha hb
    | true =>
      simp only [d127654, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127655 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127655, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127655, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127656 q = 1) (hb : d162796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127656, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127656, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127657 q = 1) (hb : d162797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127657, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127657, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127658 q = 1) (hb : d162798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127658, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127658, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127695 q = 1) (hb : d162827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127695, d162827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127695, d162827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33509 (p : Pattern) (ha : d127696 p = 1) (hb : d162828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127654 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127654, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33498 q ha hb
    | true =>
      simp only [d127654, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127655 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127655, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127655, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127587 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33483 q ha hb
    | true =>
      simp only [d127587, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127588 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127588, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127660 q = 1) (hb : d162800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127660, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127660, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127661 q = 1) (hb : d162801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127661, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127661, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127662 q = 1) (hb : d162802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127662, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127662, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127696 q = 1) (hb : d162828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127696, d162828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127696, d162828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33510 (p : Pattern) (ha : d127699 p = 1) (hb : d162831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127672 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127672, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33501 q ha hb
    | true =>
      simp only [d127672, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127673 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127673, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127673, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127674 q = 1) (hb : d162806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127674, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127674, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127675 q = 1) (hb : d162807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127675, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127675, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127676 q = 1) (hb : d162808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127676, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127676, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127699 q = 1) (hb : d162831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127699, d162831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127699, d162831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33511 (p : Pattern) (ha : d127705 p = 1) (hb : d162837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127620 q = 1) (hb : d162766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127620, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33490 q ha hb
    | true =>
      simp only [d127620, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33491 q ha hb
  have h2 (q : Pattern) (ha : d127621 q = 1) (hb : d162767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127621, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127621, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127622 q = 1) (hb : d162768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127622, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127622, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127623 q = 1) (hb : d162769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127623, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127623, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127630 q = 1) (hb : d162776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127630, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33492 q ha hb
    | true =>
      simp only [d127630, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33493 q ha hb
  have h6 (q : Pattern) (ha : d127631 q = 1) (hb : d162777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127631, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127631, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127632 q = 1) (hb : d162778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127632, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127632, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127664 q = 1) (hb : d162804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127664, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33499 q ha hb
    | true =>
      simp only [d127664, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33500 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d127665 q = 1) (hb : d162805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127665, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127665, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d127678 q = 1) (hb : d162810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127678, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33502 q ha hb
    | true =>
      simp only [d127678, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127679 q = 1) (hb : d162811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127679, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127679, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127680 q = 1) (hb : d162812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127680, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127680, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127681 q = 1) (hb : d162813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127681, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127681, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127682 q = 1) (hb : d162814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127682, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127682, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d127686 q = 1) (hb : d162818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127686, d162818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33504 q ha hb
    | true =>
      simp only [d127686, d162818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33505 q ha hb
  have h17 (q : Pattern) (ha : d127687 q = 1) (hb : d162819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127687, d162819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127687, d162819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127688 q = 1) (hb : d162820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127688, d162820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127688, d162820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d127689 q = 1) (hb : d162821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127689, d162821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127689, d162821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d127692 q = 1) (hb : d162824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127692, d162824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33506 q ha hb
    | true =>
      simp only [d127692, d162824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33507 q ha hb
  have h21 (q : Pattern) (ha : d127693 q = 1) (hb : d162825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127693, d162825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127693, d162825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d127694 q = 1) (hb : d162826 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127694, d162826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d127694, d162826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d127697 q = 1) (hb : d162829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127697, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33508 q ha hb
    | true =>
      simp only [d127697, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33509 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d127607 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d127698 q = 1) (hb : d162830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127698, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d127698, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d127700 q = 1) (hb : d162832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127700, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33510 q ha hb
    | true =>
      simp only [d127700, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d127701 q = 1) (hb : d162833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127701, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d127701, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d127702 q = 1) (hb : d162834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127702, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d127702, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d127703 q = 1) (hb : d162835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127703, d162835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d127703, d162835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d127704 q = 1) (hb : d162836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127704, d162836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127704, d162836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d127705 q = 1) (hb : d162837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127705, d162837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127705, d162837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro33512 (p : Pattern) (ha : d127717 p = 1) (hb : d162849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127707 q = 1) (hb : d162839 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127707, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33500 q ha hb
    | true =>
      simp only [d127707, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33485 q ha hb
  have h2 (q : Pattern) (ha : d127708 q = 1) (hb : d162840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127708, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127708, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127709 q = 1) (hb : d162841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127709, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127709, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127710 q = 1) (hb : d162842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127710, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127710, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127711 q = 1) (hb : d162843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127711, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127711, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127712 q = 1) (hb : d162844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127712, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33485 q ha hb
    | true =>
      simp only [d127712, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127713 q = 1) (hb : d162845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127713, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127713, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127714 q = 1) (hb : d162846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127714, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127714, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127715 q = 1) (hb : d162847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127715, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127715, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127716 q = 1) (hb : d162848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127716, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127716, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127717 q = 1) (hb : d162849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127717, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127717, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33513 (p : Pattern) (ha : d127723 p = 1) (hb : d162855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127712 q = 1) (hb : d162844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127712, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33485 q ha hb
    | true =>
      simp only [d127712, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127713 q = 1) (hb : d162845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127713, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127713, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127714 q = 1) (hb : d162846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127714, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127714, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127715 q = 1) (hb : d162847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127715, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127715, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127716 q = 1) (hb : d162848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127716, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127716, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127718 q = 1) (hb : d162850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127718, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33488 q ha hb
    | true =>
      simp only [d127718, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127719 q = 1) (hb : d162851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127719, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127719, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127720 q = 1) (hb : d162852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127720, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127720, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127721 q = 1) (hb : d162853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127721, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127721, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127722 q = 1) (hb : d162854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127722, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127722, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127723 q = 1) (hb : d162855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127723, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127723, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33514 (p : Pattern) (ha : d127730 p = 1) (hb : d162862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127697 q = 1) (hb : d162829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127697, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33508 q ha hb
    | true =>
      simp only [d127697, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33509 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127607 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127698 q = 1) (hb : d162830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127698, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127698, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d127700 q = 1) (hb : d162832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127700, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33510 q ha hb
    | true =>
      simp only [d127700, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127701 q = 1) (hb : d162833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127701, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127701, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127702 q = 1) (hb : d162834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127702, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127702, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127728 q = 1) (hb : d162860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127728, d162860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127728, d162860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127729 q = 1) (hb : d162861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127729, d162861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127729, d162861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127730 q = 1) (hb : d162862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127730, d162862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127730, d162862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33515 (p : Pattern) (ha : d127732 p = 1) (hb : d162864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127718 q = 1) (hb : d162850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127718, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33488 q ha hb
    | true =>
      simp only [d127718, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127719 q = 1) (hb : d162851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127719, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127719, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127720 q = 1) (hb : d162852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127720, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127720, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127721 q = 1) (hb : d162853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127721, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127721, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127722 q = 1) (hb : d162854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127722, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127722, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127732 q = 1) (hb : d162864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127732, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127732, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33516 (p : Pattern) (ha : d13495 p = 1) (hb : d127756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13487 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10101 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13488 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13489 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13489, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13490 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
  have h8 (q : Pattern) (ha : d13351 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
    | true =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13491 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13491, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13352 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13492 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13492, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13493 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13493, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13494 q = 1) (hb : d127755 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, d127755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13494, d127755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13495 q = 1) (hb : d127756 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13495, d127756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13495, d127756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33517 (p : Pattern) (ha : d127744 p = 1) (hb : d162870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d127740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17008 q = 1) (hb : d127742 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d127742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17008, d127742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127743 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127744 q = 1) (hb : d162870 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127744, d162870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d127744, d162870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro33518 (p : Pattern) (ha : d127751 p = 1) (hb : d162872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22508 q = 1) (hb : d127745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33478 q ha hb
  have h8 (q : Pattern) (ha : d22220 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33478 q ha hb
    | true =>
      simp only [d22220, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22509 q = 1) (hb : d127746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22509, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22221 q = 1) (hb : d101503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d101503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22221, d101503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22510 q = 1) (hb : d127747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d127747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22510, d127747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22511 q = 1) (hb : d127748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d127748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22511, d127748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d127749 q = 1) (hb : d162871 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127749, d162871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d127749, d162871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127750 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127751 q = 1) (hb : d162872 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127751, d162872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127751, d162872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro33519 (p : Pattern) (ha : d127766 p = 1) (hb : d162881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22529 q = 1) (hb : d127761 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33480 q ha hb
  have h8 (q : Pattern) (ha : d22233 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33480 q ha hb
    | true =>
      simp only [d22233, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22530 q = 1) (hb : d127762 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22530, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22234 q = 1) (hb : d101544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d101544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22234, d101544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22531 q = 1) (hb : d127763 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d127763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22531, d127763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22532 q = 1) (hb : d127764 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d127764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22532, d127764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d127765 q = 1) (hb : d162880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127765, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d127765, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127766 q = 1) (hb : d162881 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127766, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127766, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro33520 (p : Pattern) (ha : d127775 p = 1) (hb : d162890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127752 q = 1) (hb : d162873 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127752, d162873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33517 q ha hb
    | true =>
      simp only [d127752, d162873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33518 q ha hb
  have h2 (q : Pattern) (ha : d127753 q = 1) (hb : d162874 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127753, d162874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127753, d162874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127754 q = 1) (hb : d162875 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127754, d162875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127754, d162875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127757 q = 1) (hb : d162876 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127757, d162876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33518 q ha hb
    | true =>
      simp only [d127757, d162876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33516 q hb ha
  have h5 (q : Pattern) (ha : d127758 q = 1) (hb : d162877 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127758, d162877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127758, d162877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127759 q = 1) (hb : d162878 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127759, d162878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127759, d162878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127760 q = 1) (hb : d162879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127760, d162879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127760, d162879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127767 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33518 q ha hb
    | true =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
  have h9 (q : Pattern) (ha : d127768 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127769 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127770 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22338 q hb ha
  have h12 (q : Pattern) (ha : d127771 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127772 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127773 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127774 q = 1) (hb : d162889 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127774, d162889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127774, d162889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d127775 q = 1) (hb : d162890 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127775, d162890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127775, d162890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro33521 (p : Pattern) (ha : d127780 p = 1) (hb : d162895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127767 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33518 q ha hb
    | true =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
  have h2 (q : Pattern) (ha : d127768 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127769 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127770 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22338 q hb ha
  have h5 (q : Pattern) (ha : d127771 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127772 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127773 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127778 q = 1) (hb : d162893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127778, d162893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127778, d162893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127779 q = 1) (hb : d162894 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127779, d162894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127779, d162894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127780 q = 1) (hb : d162895 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127780, d162895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127780, d162895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro33522 (p : Pattern) (ha : d127786 p = 1) (hb : d162901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127776 q = 1) (hb : d162891 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127776, d162891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33520 q ha hb
    | true =>
      simp only [d127776, d162891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127777 q = 1) (hb : d162892 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127777, d162892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127777, d162892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127781 q = 1) (hb : d162896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127781, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33521 q ha hb
    | true =>
      simp only [d127781, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127782 q = 1) (hb : d162897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127782, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127782, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127783 q = 1) (hb : d162898 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127783, d162898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127783, d162898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127784 q = 1) (hb : d162899 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127784, d162899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127784, d162899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127785 q = 1) (hb : d162900 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127785, d162900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127785, d162900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127786 q = 1) (hb : d162901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127786, d162901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127786, d162901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33523 (p : Pattern) (ha : d127792 p = 1) (hb : d162907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127787 q = 1) (hb : d162902 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127787, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127787, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22341 q hb ha
  have h2 (q : Pattern) (ha : d127788 q = 1) (hb : d162903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127788, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127788, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127789 q = 1) (hb : d162904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127789, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127789, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127790 q = 1) (hb : d162905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127790, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127790, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127791 q = 1) (hb : d162906 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127791, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127791, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127792 q = 1) (hb : d162907 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127792, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127792, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33524 (p : Pattern) (ha : d127798 p = 1) (hb : d162913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127781 q = 1) (hb : d162896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127781, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33521 q ha hb
    | true =>
      simp only [d127781, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127782 q = 1) (hb : d162897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127782, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127782, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127793 q = 1) (hb : d162908 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127793, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33523 q ha hb
    | true =>
      simp only [d127793, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127794 q = 1) (hb : d162909 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127794, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127794, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127795 q = 1) (hb : d162910 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127795, d162910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127795, d162910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127796 q = 1) (hb : d162911 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127796, d162911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127796, d162911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127797 q = 1) (hb : d162912 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127797, d162912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127797, d162912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127798 q = 1) (hb : d162913 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127798, d162913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127798, d162913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33525 (p : Pattern) (ha : d127819 p = 1) (hb : d162917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127767 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33518 q ha hb
    | true =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
  have h2 (q : Pattern) (ha : d127768 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127769 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127770 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22338 q hb ha
  have h5 (q : Pattern) (ha : d127771 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127772 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127773 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127814 q = 1) (hb : d162902 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127814, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127814, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18688 q hb ha
  have h9 (q : Pattern) (ha : d127815 q = 1) (hb : d162903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127815, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127815, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127816 q = 1) (hb : d162904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127816, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127816, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127817 q = 1) (hb : d162905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127817, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127817, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127818 q = 1) (hb : d162916 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127818, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127818, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127819 q = 1) (hb : d162917 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127819, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127819, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33526 (p : Pattern) (ha : d127825 p = 1) (hb : d162923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127820 q = 1) (hb : d162918 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127820, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33525 q ha hb
    | true =>
      simp only [d127820, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127821 q = 1) (hb : d162919 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127821, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127821, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127822 q = 1) (hb : d162920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127822, d162920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127822, d162920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127823 q = 1) (hb : d162921 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127823, d162921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127823, d162921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127824 q = 1) (hb : d162922 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127824, d162922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127824, d162922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127825 q = 1) (hb : d162923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127825, d162923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127825, d162923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33527 (p : Pattern) (ha : d127831 p = 1) (hb : d162929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127799 q = 1) (hb : d162914 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127799, d162914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33522 q ha hb
    | true =>
      simp only [d127799, d162914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33524 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127812 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127813 q = 1) (hb : d162915 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127813, d162915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127813, d162915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d127826 q = 1) (hb : d162924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127826, d162924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33526 q ha hb
    | true =>
      simp only [d127826, d162924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127827 q = 1) (hb : d162925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127827, d162925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127827, d162925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127828 q = 1) (hb : d162926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127828, d162926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127828, d162926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127829 q = 1) (hb : d162927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127829, d162927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127829, d162927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127830 q = 1) (hb : d162928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127830, d162928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127830, d162928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127831 q = 1) (hb : d162929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127831, d162929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127831, d162929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33528 (p : Pattern) (ha : d127811 p = 1) (hb : d162934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127793 q = 1) (hb : d162908 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127793, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33523 q ha hb
    | true =>
      simp only [d127793, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127794 q = 1) (hb : d162909 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127794, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127794, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127808 q = 1) (hb : d162931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127808, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127808, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127809 q = 1) (hb : d162932 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127809, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127809, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127810 q = 1) (hb : d162933 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127810, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127810, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127811 q = 1) (hb : d162934 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127811, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127811, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33529 (p : Pattern) (ha : d127838 p = 1) (hb : d162940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127833 q = 1) (hb : d162935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127833, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33528 q ha hb
    | true =>
      simp only [d127833, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127834 q = 1) (hb : d162936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127834, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127834, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127835 q = 1) (hb : d162937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127835, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127835, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127836 q = 1) (hb : d162938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127836, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127836, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127837 q = 1) (hb : d162939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127837, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127837, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127838 q = 1) (hb : d162940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127838, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127838, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33530 (p : Pattern) (ha : d127844 p = 1) (hb : d162946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127603 q = 1) (hb : d162749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127603, d162749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127603, d162749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33486 q ha hb
  have h2 (q : Pattern) (ha : d127604 q = 1) (hb : d162750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127604, d162750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127604, d162750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d127613 q = 1) (hb : d162759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127613, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33486 q ha hb
    | true =>
      simp only [d127613, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33489 q ha hb
  have h4 (q : Pattern) (ha : d127614 q = 1) (hb : d162760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127614, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127614, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127615 q = 1) (hb : d162761 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127615, d162761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127615, d162761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127706 q = 1) (hb : d162838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127706, d162838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33503 q ha hb
    | true =>
      simp only [d127706, d162838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33511 q ha hb
  have h7 (q : Pattern) (ha : d127724 q = 1) (hb : d162856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127724, d162856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33512 q ha hb
    | true =>
      simp only [d127724, d162856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33513 q ha hb
  have h8 (q : Pattern) (ha : d127725 q = 1) (hb : d162857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127725, d162857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127725, d162857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127726 q = 1) (hb : d162858 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127726, d162858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127726, d162858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d127727 q = 1) (hb : d162859 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127727, d162859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127727, d162859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127731 q = 1) (hb : d162863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127731, d162863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127731, d162863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33514 q ha hb
  have h12 (q : Pattern) (ha : d127733 q = 1) (hb : d162865 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127733, d162865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127733, d162865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33515 q ha hb
  have h13 (q : Pattern) (ha : d127734 q = 1) (hb : d162866 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127734, d162866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127734, d162866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127735 q = 1) (hb : d162867 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127735, d162867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127735, d162867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d127736 q = 1) (hb : d162868 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127736, d162868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d127736, d162868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d127737 q = 1) (hb : d162869 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127737, d162869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127737, d162869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d127832 q = 1) (hb : d162930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127832, d162930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127832, d162930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33527 q ha hb
  have h18 (q : Pattern) (ha : d127839 q = 1) (hb : d162941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127839, d162941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127839, d162941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33529 q ha hb
  have h19 (q : Pattern) (ha : d127840 q = 1) (hb : d162942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127840, d162942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127840, d162942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d127841 q = 1) (hb : d162943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127841, d162943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127841, d162943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d127842 q = 1) (hb : d162944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127842, d162944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d127842, d162944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d127843 q = 1) (hb : d162945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127843, d162945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d127843, d162945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d127844 q = 1) (hb : d162946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127844, d162946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127844, d162946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro33531 (p : Pattern) (ha : d127850 p = 1) (hb : d162952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127845 q = 1) (hb : d162947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127845, d162947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127845, d162947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33530 q ha hb
  have h2 (q : Pattern) (ha : d127846 q = 1) (hb : d162948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127846, d162948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127846, d162948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127847 q = 1) (hb : d162949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127847, d162949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127847, d162949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127848 q = 1) (hb : d162950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127848, d162950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127848, d162950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127849 q = 1) (hb : d162951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127849, d162951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127849, d162951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127850 q = 1) (hb : d162952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127850, d162952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127850, d162952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33532 (p : Pattern) (ha : d127859 p = 1) (hb : d162957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d127855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d127856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17155 q = 1) (hb : d127857 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d127857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17155, d127857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127858 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127859 q = 1) (hb : d162957 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127859, d162957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127859, d162957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro33533 (p : Pattern) (ha : d22687 p = 1) (hb : d101711 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d2041 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h5 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h6 (q : Pattern) (ha : d2044 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2045 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2050 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2051 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d22687 q = 1) (hb : d101711 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22687, d101711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22687, d101711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro33534 (p : Pattern) (ha : d127863 p = 1) (hb : d162959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33533 q ha hb
    | true =>
      simp only [d22688, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d127860 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d127860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d127860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d127861 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d127861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d127861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d127862 q = 1) (hb : d162958 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127862, d162958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127862, d162958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127863 q = 1) (hb : d162959 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127863, d162959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127863, d162959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro33535 (p : Pattern) (ha : d127876 p = 1) (hb : d162972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127864 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33532 q ha hb
    | true =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
  have h2 (q : Pattern) (ha : d127865 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127866 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127867 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22368 q hb ha
  have h5 (q : Pattern) (ha : d127868 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127869 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127870 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127871 q = 1) (hb : d162967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127871, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127871, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22351 q hb ha
  have h9 (q : Pattern) (ha : d127872 q = 1) (hb : d162968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127872, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127872, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127873 q = 1) (hb : d162969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127873, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127873, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127874 q = 1) (hb : d162970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127874, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127874, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127875 q = 1) (hb : d162971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127875, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127875, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127876 q = 1) (hb : d162972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127876, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127876, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33536 (p : Pattern) (ha : d127880 p = 1) (hb : d162976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127871 q = 1) (hb : d162967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127871, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127871, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22351 q hb ha
  have h2 (q : Pattern) (ha : d127872 q = 1) (hb : d162968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127872, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127872, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127873 q = 1) (hb : d162969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127873, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127873, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127874 q = 1) (hb : d162970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127874, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127874, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127879 q = 1) (hb : d162975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127879, d162975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127879, d162975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127880 q = 1) (hb : d162976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127880, d162976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127880, d162976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33537 (p : Pattern) (ha : d127886 p = 1) (hb : d162982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127877 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33535 q ha hb
    | true =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127878 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127883 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127884 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127885 q = 1) (hb : d162981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127885, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127885, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127886 q = 1) (hb : d162982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127886, d162982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127886, d162982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33538 (p : Pattern) (ha : d127890 p = 1) (hb : d162986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127887 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127888 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127889 q = 1) (hb : d162985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127889, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127889, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127890 q = 1) (hb : d162986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127890, d162986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127890, d162986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33539 (p : Pattern) (ha : d127896 p = 1) (hb : d162992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127891 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33537 q ha hb
    | true =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
  have h2 (q : Pattern) (ha : d127892 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127892, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127892, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127893 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127893, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127893, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127894 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127894, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127894, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127895 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127895, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127895, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127896 q = 1) (hb : d162992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127896, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127896, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33540 (p : Pattern) (ha : d127899 p = 1) (hb : d162995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127877 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33535 q ha hb
    | true =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127878 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127883 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127884 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127885 q = 1) (hb : d162981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127885, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127885, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127899 q = 1) (hb : d162995 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127899, d162995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127899, d162995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33541 (p : Pattern) (ha : d127900 p = 1) (hb : d162996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127887 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127888 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127889 q = 1) (hb : d162985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127889, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127889, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127900 q = 1) (hb : d162996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127900, d162996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127900, d162996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33542 (p : Pattern) (ha : d127906 p = 1) (hb : d163002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127891 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33537 q ha hb
    | true =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
  have h2 (q : Pattern) (ha : d127892 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127892, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127892, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127893 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127893, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127893, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127894 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127894, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127894, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127895 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127895, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127895, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127901 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127901, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33540 q ha hb
    | true =>
      simp only [d127901, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33541 q ha hb
  have h7 (q : Pattern) (ha : d127902 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127902, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127902, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127903 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127903, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127903, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127904 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127904, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127904, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127905 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127905, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127905, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127906 q = 1) (hb : d163002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127906, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127906, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33543 (p : Pattern) (ha : d127911 p = 1) (hb : d163007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127877 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33535 q ha hb
    | true =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127878 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127883 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127884 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127910 q = 1) (hb : d163006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127910, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127910, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127911 q = 1) (hb : d163007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127911, d163007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127911, d163007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33544 (p : Pattern) (ha : d127913 p = 1) (hb : d163009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127887 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127888 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127912 q = 1) (hb : d163008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127912, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127912, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127913 q = 1) (hb : d163009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127913, d163009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127913, d163009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33545 (p : Pattern) (ha : d127920 p = 1) (hb : d163016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127877 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33535 q ha hb
    | true =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127878 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127883 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127918 q = 1) (hb : d163014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127918, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127918, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127919 q = 1) (hb : d163015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127919, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127919, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127920 q = 1) (hb : d163016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127920, d163016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127920, d163016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33546 (p : Pattern) (ha : d127923 p = 1) (hb : d163019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127887 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127921 q = 1) (hb : d163017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127921, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127921, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127922 q = 1) (hb : d163018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127922, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127922, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127923 q = 1) (hb : d163019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127923, d163019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127923, d163019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33547 (p : Pattern) (ha : d13677 p = 1) (hb : d101691 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13677 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d101691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13677, d101691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33548 (p : Pattern) (ha : d13683 p = 1) (hb : d127935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d127858 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d127858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, d127858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13683 q = 1) (hb : d127935 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13683, d127935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13683, d127935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33549 (p : Pattern) (ha : d127931 p = 1) (hb : d163023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d53425 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17225 q = 1) (hb : d127927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17226 q = 1) (hb : d127928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17227 q = 1) (hb : d127929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d127929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17227, d127929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127930 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127931 q = 1) (hb : d163023 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127931, d163023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127931, d163023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro33550 (p : Pattern) (ha : d127941 p = 1) (hb : d163032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127932 q = 1) (hb : d163024 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127932, d163024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33549 q ha hb
    | true =>
      simp only [d127932, d163024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33532 q ha hb
  have h2 (q : Pattern) (ha : d127933 q = 1) (hb : d163025 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127933, d163025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127933, d163025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127934 q = 1) (hb : d163026 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127934, d163026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127934, d163026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127936 q = 1) (hb : d163027 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127936, d163027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33532 q ha hb
    | true =>
      simp only [d127936, d163027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33548 q hb ha
  have h5 (q : Pattern) (ha : d127937 q = 1) (hb : d163028 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127937, d163028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127937, d163028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127938 q = 1) (hb : d163029 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127938, d163029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127938, d163029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127939 q = 1) (hb : d163030 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127939, d163030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127939, d163030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127864 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33532 q ha hb
    | true =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
  have h9 (q : Pattern) (ha : d127865 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127866 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127867 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22368 q hb ha
  have h12 (q : Pattern) (ha : d127868 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127869 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127870 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127940 q = 1) (hb : d163031 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127940, d163031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127940, d163031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d127941 q = 1) (hb : d163032 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127941, d163032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127941, d163032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro33551 (p : Pattern) (ha : d127946 p = 1) (hb : d163037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127864 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33532 q ha hb
    | true =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
  have h2 (q : Pattern) (ha : d127865 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127866 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127867 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22368 q hb ha
  have h5 (q : Pattern) (ha : d127868 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127869 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127870 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127944 q = 1) (hb : d163035 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127944, d163035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127944, d163035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127945 q = 1) (hb : d163036 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127945, d163036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127945, d163036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127946 q = 1) (hb : d163037 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127946, d163037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127946, d163037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro33552 (p : Pattern) (ha : d127952 p = 1) (hb : d163043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127942 q = 1) (hb : d163033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127942, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33550 q ha hb
    | true =>
      simp only [d127942, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127943 q = 1) (hb : d163034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127943, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127943, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127947 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33551 q ha hb
    | true =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127948 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127949 q = 1) (hb : d163040 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127949, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127949, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127950 q = 1) (hb : d163041 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127950, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127950, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127951 q = 1) (hb : d163042 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127951, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127951, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127952 q = 1) (hb : d163043 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127952, d163043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127952, d163043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33553 (p : Pattern) (ha : d127956 p = 1) (hb : d163047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127947 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33551 q ha hb
    | true =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127948 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127953 q = 1) (hb : d163044 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127953, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127953, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127954 q = 1) (hb : d163045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127954, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127954, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127955 q = 1) (hb : d163046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127955, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127955, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127956 q = 1) (hb : d163047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127956, d163047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127956, d163047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33554 (p : Pattern) (ha : d127964 p = 1) (hb : d162972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127864 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33532 q ha hb
    | true =>
      simp only [d127864, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
  have h2 (q : Pattern) (ha : d127865 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127865, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127866 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127866, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127867 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127867, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22368 q hb ha
  have h5 (q : Pattern) (ha : d127868 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127868, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127869 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127869, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127870 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127870, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127959 q = 1) (hb : d162967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127959, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33534 q ha hb
    | true =>
      simp only [d127959, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18730 q hb ha
  have h9 (q : Pattern) (ha : d127960 q = 1) (hb : d162968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127960, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127960, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127961 q = 1) (hb : d162969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127961, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127961, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127962 q = 1) (hb : d162970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127962, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127962, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127963 q = 1) (hb : d162971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127963, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127963, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127964 q = 1) (hb : d162972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127964, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127964, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33555 (p : Pattern) (ha : d127970 p = 1) (hb : d163053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127965 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127965, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33554 q ha hb
    | true =>
      simp only [d127965, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127966 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127966, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127966, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127967 q = 1) (hb : d163050 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127967, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127967, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127968 q = 1) (hb : d163051 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127968, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127968, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127969 q = 1) (hb : d163052 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127969, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127969, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127970 q = 1) (hb : d163053 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127970, d163053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127970, d163053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33556 (p : Pattern) (ha : d127976 p = 1) (hb : d163059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127914 q = 1) (hb : d163010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127914, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33543 q ha hb
    | true =>
      simp only [d127914, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33544 q ha hb
  have h2 (q : Pattern) (ha : d127915 q = 1) (hb : d163011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127915, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127915, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127916 q = 1) (hb : d163012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127916, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127916, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127917 q = 1) (hb : d163013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127917, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127917, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127924 q = 1) (hb : d163020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127924, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33545 q ha hb
    | true =>
      simp only [d127924, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33546 q ha hb
  have h6 (q : Pattern) (ha : d127925 q = 1) (hb : d163021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127925, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127925, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127926 q = 1) (hb : d163022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127926, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127926, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127957 q = 1) (hb : d163048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127957, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33552 q ha hb
    | true =>
      simp only [d127957, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33553 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127891 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d127958 q = 1) (hb : d163049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127958, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127958, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d127971 q = 1) (hb : d163054 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127971, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33555 q ha hb
    | true =>
      simp only [d127971, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127972 q = 1) (hb : d163055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127972, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127972, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127973 q = 1) (hb : d163056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127973, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127973, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127974 q = 1) (hb : d163057 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127974, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127974, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127975 q = 1) (hb : d163058 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127975, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127975, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d127976 q = 1) (hb : d163059 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127976, d163059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127976, d163059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro33557 (p : Pattern) (ha : d127977 p = 1) (hb : d163060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127877 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33535 q ha hb
    | true =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127878 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127883 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127884 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127884, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127910 q = 1) (hb : d163006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127910, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127910, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127977 q = 1) (hb : d163060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127977, d163060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127977, d163060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33558 (p : Pattern) (ha : d127978 p = 1) (hb : d163061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127887 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127888 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127888, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127912 q = 1) (hb : d163008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127912, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127912, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127978 q = 1) (hb : d163061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127978, d163061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127978, d163061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33559 (p : Pattern) (ha : d127983 p = 1) (hb : d163066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127877 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33535 q ha hb
    | true =>
      simp only [d127877, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127878 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127878, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127883 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127883, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127918 q = 1) (hb : d163014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127918, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127918, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127919 q = 1) (hb : d163015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127919, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127919, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127983 q = 1) (hb : d163066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127983, d163066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127983, d163066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33560 (p : Pattern) (ha : d127984 p = 1) (hb : d163067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127887 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127887, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127921 q = 1) (hb : d163017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127921, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127921, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127922 q = 1) (hb : d163018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127922, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127922, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127984 q = 1) (hb : d163067 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127984, d163067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127984, d163067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33561 (p : Pattern) (ha : d127988 p = 1) (hb : d163071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127942 q = 1) (hb : d163033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127942, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33550 q ha hb
    | true =>
      simp only [d127942, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127943 q = 1) (hb : d163034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127943, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127943, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127947 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33551 q ha hb
    | true =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127948 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127949 q = 1) (hb : d163040 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127949, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127949, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127950 q = 1) (hb : d163041 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127950, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127950, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127951 q = 1) (hb : d163042 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127951, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127951, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127988 q = 1) (hb : d163071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127988, d163071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127988, d163071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33562 (p : Pattern) (ha : d127989 p = 1) (hb : d163072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127947 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33551 q ha hb
    | true =>
      simp only [d127947, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127948 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127948, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127881 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33536 q ha hb
    | true =>
      simp only [d127881, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127882 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127882, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127953 q = 1) (hb : d163044 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127953, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127953, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127954 q = 1) (hb : d163045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127954, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127954, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127955 q = 1) (hb : d163046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127955, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127955, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127989 q = 1) (hb : d163072 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127989, d163072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127989, d163072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33563 (p : Pattern) (ha : d127992 p = 1) (hb : d163075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127965 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127965, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33554 q ha hb
    | true =>
      simp only [d127965, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127966 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127966, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127966, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127967 q = 1) (hb : d163050 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127967, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127967, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127968 q = 1) (hb : d163051 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127968, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127968, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127969 q = 1) (hb : d163052 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127969, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127969, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127992 q = 1) (hb : d163075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127992, d163075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127992, d163075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33564 (p : Pattern) (ha : d127998 p = 1) (hb : d163081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127914 q = 1) (hb : d163010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127914, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33543 q ha hb
    | true =>
      simp only [d127914, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33544 q ha hb
  have h2 (q : Pattern) (ha : d127915 q = 1) (hb : d163011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127915, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127915, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127916 q = 1) (hb : d163012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127916, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127916, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127917 q = 1) (hb : d163013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127917, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127917, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127924 q = 1) (hb : d163020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127924, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33545 q ha hb
    | true =>
      simp only [d127924, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33546 q ha hb
  have h6 (q : Pattern) (ha : d127925 q = 1) (hb : d163021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127925, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127925, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127926 q = 1) (hb : d163022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127926, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127926, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127957 q = 1) (hb : d163048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127957, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33552 q ha hb
    | true =>
      simp only [d127957, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33553 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127891 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d127958 q = 1) (hb : d163049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127958, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127958, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d127971 q = 1) (hb : d163054 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127971, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33555 q ha hb
    | true =>
      simp only [d127971, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127972 q = 1) (hb : d163055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127972, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127972, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127973 q = 1) (hb : d163056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127973, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127973, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127974 q = 1) (hb : d163057 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127974, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127974, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127975 q = 1) (hb : d163058 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127975, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127975, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d127979 q = 1) (hb : d163062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127979, d163062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33557 q ha hb
    | true =>
      simp only [d127979, d163062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33558 q ha hb
  have h17 (q : Pattern) (ha : d127980 q = 1) (hb : d163063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127980, d163063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127980, d163063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127981 q = 1) (hb : d163064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127981, d163064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127981, d163064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d127982 q = 1) (hb : d163065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127982, d163065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127982, d163065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d127985 q = 1) (hb : d163068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127985, d163068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33559 q ha hb
    | true =>
      simp only [d127985, d163068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33560 q ha hb
  have h21 (q : Pattern) (ha : d127986 q = 1) (hb : d163069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127986, d163069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127986, d163069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d127987 q = 1) (hb : d163070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127987, d163070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d127987, d163070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d127990 q = 1) (hb : d163073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127990, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33561 q ha hb
    | true =>
      simp only [d127990, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33562 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d127901 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d127991 q = 1) (hb : d163074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127991, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d127991, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d127993 q = 1) (hb : d163076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127993, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33563 q ha hb
    | true =>
      simp only [d127993, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d127994 q = 1) (hb : d163077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127994, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d127994, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d127995 q = 1) (hb : d163078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127995, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d127995, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d127996 q = 1) (hb : d163079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127996, d163079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d127996, d163079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d127997 q = 1) (hb : d163080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127997, d163080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127997, d163080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d127998 q = 1) (hb : d163081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127998, d163081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127998, d163081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro33565 (p : Pattern) (ha : d128010 p = 1) (hb : d163093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128000 q = 1) (hb : d163083 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128000, d163083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33553 q ha hb
    | true =>
      simp only [d128000, d163083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
  have h2 (q : Pattern) (ha : d128001 q = 1) (hb : d163084 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128001, d163084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128001, d163084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128002 q = 1) (hb : d163085 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128002, d163085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128002, d163085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128003 q = 1) (hb : d163086 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128003, d163086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128003, d163086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128004 q = 1) (hb : d163087 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128004, d163087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128004, d163087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128005 q = 1) (hb : d163088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128005, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
    | true =>
      simp only [d128005, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128006 q = 1) (hb : d163089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128006, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128006, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128007 q = 1) (hb : d163090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128007, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128007, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128008 q = 1) (hb : d163091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128008, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128008, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128009 q = 1) (hb : d163092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128009, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128009, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128010 q = 1) (hb : d163093 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128010, d163093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128010, d163093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33566 (p : Pattern) (ha : d128016 p = 1) (hb : d163099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128005 q = 1) (hb : d163088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128005, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
    | true =>
      simp only [d128005, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128006 q = 1) (hb : d163089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128006, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128006, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128007 q = 1) (hb : d163090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128007, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128007, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128008 q = 1) (hb : d163091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128008, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128008, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128009 q = 1) (hb : d163092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128009, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128009, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128011 q = 1) (hb : d163094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128011, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33541 q ha hb
    | true =>
      simp only [d128011, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128012 q = 1) (hb : d163095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128012, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128012, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128013 q = 1) (hb : d163096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128013, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128013, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128014 q = 1) (hb : d163097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128014, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128014, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128015 q = 1) (hb : d163098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128015, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128015, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128016 q = 1) (hb : d163099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128016, d163099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128016, d163099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33567 (p : Pattern) (ha : d128023 p = 1) (hb : d163106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127990 q = 1) (hb : d163073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127990, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33561 q ha hb
    | true =>
      simp only [d127990, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33562 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127991 q = 1) (hb : d163074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127991, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127991, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d127993 q = 1) (hb : d163076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127993, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33563 q ha hb
    | true =>
      simp only [d127993, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127994 q = 1) (hb : d163077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127994, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127994, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d127995 q = 1) (hb : d163078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127995, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127995, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128021 q = 1) (hb : d163104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128021, d163104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128021, d163104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128022 q = 1) (hb : d163105 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128022, d163105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128022, d163105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128023 q = 1) (hb : d163106 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128023, d163106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128023, d163106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33568 (p : Pattern) (ha : d128025 p = 1) (hb : d163108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128011 q = 1) (hb : d163094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128011, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33541 q ha hb
    | true =>
      simp only [d128011, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128012 q = 1) (hb : d163095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128012, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128012, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128013 q = 1) (hb : d163096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128013, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128013, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128014 q = 1) (hb : d163097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128014, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128014, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128015 q = 1) (hb : d163098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128015, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128015, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128025 q = 1) (hb : d163108 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128025, d163108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128025, d163108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33569 (p : Pattern) (ha : d13822 p = 1) (hb : d128048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13822 q = 1) (hb : d128048 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13822, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13822, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33570 (p : Pattern) (ha : d128037 p = 1) (hb : d163114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h8 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17371 q = 1) (hb : d128033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17372 q = 1) (hb : d128034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17373 q = 1) (hb : d128035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d128035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17373, d128035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d128036 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128037 q = 1) (hb : d163114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128037, d163114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d128037, d163114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro33571 (p : Pattern) (ha : d128044 p = 1) (hb : d163115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2337 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d128040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17380 q = 1) (hb : d128042 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d128042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17380, d128042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128044 q = 1) (hb : d163115 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128044, d163115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d128044, d163115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro33572 (p : Pattern) (ha : d128058 p = 1) (hb : d163124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d128053 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33533 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33533 q ha hb
    | true =>
      simp only [d22688, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d128054 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d128055 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d128055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d128055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d128056 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d128056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d128056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d128057 q = 1) (hb : d163123 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128057, d163123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d128057, d163123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128058 q = 1) (hb : d163124 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128058, d163124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128058, d163124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro33573 (p : Pattern) (ha : d128067 p = 1) (hb : d163133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128045 q = 1) (hb : d163116 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128045, d163116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33570 q ha hb
    | true =>
      simp only [d128045, d163116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33571 q ha hb
  have h2 (q : Pattern) (ha : d128046 q = 1) (hb : d163117 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128046, d163117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128046, d163117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128047 q = 1) (hb : d163118 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128047, d163118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128047, d163118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128049 q = 1) (hb : d163119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128049, d163119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33571 q ha hb
    | true =>
      simp only [d128049, d163119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33569 q hb ha
  have h5 (q : Pattern) (ha : d128050 q = 1) (hb : d163120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128050, d163120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128050, d163120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128051 q = 1) (hb : d163121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128051, d163121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128051, d163121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128052 q = 1) (hb : d163122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128052, d163122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128052, d163122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128059 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33571 q ha hb
    | true =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
  have h9 (q : Pattern) (ha : d128060 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128061 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128062 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h12 (q : Pattern) (ha : d128063 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128064 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128065 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128066 q = 1) (hb : d163132 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128066, d163132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128066, d163132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128067 q = 1) (hb : d163133 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128067, d163133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128067, d163133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro33574 (p : Pattern) (ha : d128072 p = 1) (hb : d163138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128059 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33571 q ha hb
    | true =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
  have h2 (q : Pattern) (ha : d128060 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128061 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128062 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h5 (q : Pattern) (ha : d128063 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128064 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128065 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128070 q = 1) (hb : d163136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128070, d163136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128070, d163136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128071 q = 1) (hb : d163137 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128071, d163137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128071, d163137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128072 q = 1) (hb : d163138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128072, d163138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128072, d163138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro33575 (p : Pattern) (ha : d128078 p = 1) (hb : d163144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128068 q = 1) (hb : d163134 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128068, d163134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33573 q ha hb
    | true =>
      simp only [d128068, d163134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128069 q = 1) (hb : d163135 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128069, d163135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128069, d163135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128073 q = 1) (hb : d163139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128073, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33574 q ha hb
    | true =>
      simp only [d128073, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128074 q = 1) (hb : d163140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128074, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128074, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128075 q = 1) (hb : d163141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128075, d163141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128075, d163141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128076 q = 1) (hb : d163142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128076, d163142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128076, d163142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128077 q = 1) (hb : d163143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128077, d163143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128077, d163143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128078 q = 1) (hb : d163144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128078, d163144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128078, d163144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33576 (p : Pattern) (ha : d128084 p = 1) (hb : d163150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128079 q = 1) (hb : d163145 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128079, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128079, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22394 q hb ha
  have h2 (q : Pattern) (ha : d128080 q = 1) (hb : d163146 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128080, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128080, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128081 q = 1) (hb : d163147 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128081, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128081, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128082 q = 1) (hb : d163148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128082, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128082, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128083 q = 1) (hb : d163149 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128083, d163149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128083, d163149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128084 q = 1) (hb : d163150 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128084, d163150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128084, d163150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33577 (p : Pattern) (ha : d128090 p = 1) (hb : d163156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128073 q = 1) (hb : d163139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128073, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33574 q ha hb
    | true =>
      simp only [d128073, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128074 q = 1) (hb : d163140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128074, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128074, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128085 q = 1) (hb : d163151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128085, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33576 q ha hb
    | true =>
      simp only [d128085, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128086 q = 1) (hb : d163152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128086, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128086, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128087 q = 1) (hb : d163153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128087, d163153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128087, d163153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128088 q = 1) (hb : d163154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128088, d163154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128088, d163154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128089 q = 1) (hb : d163155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128089, d163155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128089, d163155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128090 q = 1) (hb : d163156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128090, d163156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128090, d163156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33578 (p : Pattern) (ha : d128111 p = 1) (hb : d163160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128059 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33571 q ha hb
    | true =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
  have h2 (q : Pattern) (ha : d128060 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128061 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128062 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h5 (q : Pattern) (ha : d128063 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128064 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128065 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128106 q = 1) (hb : d163145 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128106, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128106, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q hb ha
  have h9 (q : Pattern) (ha : d128107 q = 1) (hb : d163146 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128107, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128107, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128108 q = 1) (hb : d163147 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128108, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128108, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128109 q = 1) (hb : d163148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128109, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128109, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128110 q = 1) (hb : d163159 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128110, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128110, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128111 q = 1) (hb : d163160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128111, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128111, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33579 (p : Pattern) (ha : d128117 p = 1) (hb : d163166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128112 q = 1) (hb : d163161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128112, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33578 q ha hb
    | true =>
      simp only [d128112, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128113 q = 1) (hb : d163162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128113, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128113, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128114 q = 1) (hb : d163163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128114, d163163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128114, d163163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128115 q = 1) (hb : d163164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128115, d163164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128115, d163164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128116 q = 1) (hb : d163165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128116, d163165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128116, d163165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128117 q = 1) (hb : d163166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128117, d163166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128117, d163166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33580 (p : Pattern) (ha : d128123 p = 1) (hb : d163172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128091 q = 1) (hb : d163157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128091, d163157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33575 q ha hb
    | true =>
      simp only [d128091, d163157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33577 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d163158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d163158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128105, d163158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128118 q = 1) (hb : d163167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128118, d163167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33579 q ha hb
    | true =>
      simp only [d128118, d163167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128119 q = 1) (hb : d163168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128119, d163168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128119, d163168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128120 q = 1) (hb : d163169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d163169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d163169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128121 q = 1) (hb : d163170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d163170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d163170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128122 q = 1) (hb : d163171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d163171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d163171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128123 q = 1) (hb : d163172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d163172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d163172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33581 (p : Pattern) (ha : d128103 p = 1) (hb : d163177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128085 q = 1) (hb : d163151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128085, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33576 q ha hb
    | true =>
      simp only [d128085, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128086 q = 1) (hb : d163152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128086, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128086, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128100 q = 1) (hb : d163174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128100, d163174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128100, d163174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128101 q = 1) (hb : d163175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128101, d163175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128101, d163175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128102 q = 1) (hb : d163176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128102, d163176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128102, d163176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128103 q = 1) (hb : d163177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128103, d163177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128103, d163177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33582 (p : Pattern) (ha : d128130 p = 1) (hb : d163183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128125 q = 1) (hb : d163178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128125, d163178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33581 q ha hb
    | true =>
      simp only [d128125, d163178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128126 q = 1) (hb : d163179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128126, d163179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128126, d163179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128127 q = 1) (hb : d163180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128127, d163180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128127, d163180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128128 q = 1) (hb : d163181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128128, d163181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128128, d163181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128129 q = 1) (hb : d163182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128129, d163182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128129, d163182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128130 q = 1) (hb : d163183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128130, d163183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128130, d163183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33583 (p : Pattern) (ha : d128136 p = 1) (hb : d163189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127897 q = 1) (hb : d162993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127897, d162993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127897, d162993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33539 q ha hb
  have h2 (q : Pattern) (ha : d127898 q = 1) (hb : d162994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127898, d162994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127898, d162994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d127907 q = 1) (hb : d163003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127907, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33539 q ha hb
    | true =>
      simp only [d127907, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33542 q ha hb
  have h4 (q : Pattern) (ha : d127908 q = 1) (hb : d163004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127908, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127908, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127909 q = 1) (hb : d163005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127909, d163005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127909, d163005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127999 q = 1) (hb : d163082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127999, d163082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33556 q ha hb
    | true =>
      simp only [d127999, d163082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33564 q ha hb
  have h7 (q : Pattern) (ha : d128017 q = 1) (hb : d163100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128017, d163100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33565 q ha hb
    | true =>
      simp only [d128017, d163100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33566 q ha hb
  have h8 (q : Pattern) (ha : d128018 q = 1) (hb : d163101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128018, d163101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128018, d163101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128019 q = 1) (hb : d163102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128019, d163102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128019, d163102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128020 q = 1) (hb : d163103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128020, d163103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128020, d163103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128024 q = 1) (hb : d163107 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128024, d163107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128024, d163107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33567 q ha hb
  have h12 (q : Pattern) (ha : d128026 q = 1) (hb : d163109 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128026, d163109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128026, d163109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33568 q ha hb
  have h13 (q : Pattern) (ha : d128027 q = 1) (hb : d163110 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128027, d163110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128027, d163110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128028 q = 1) (hb : d163111 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128028, d163111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128028, d163111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128029 q = 1) (hb : d163112 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128029, d163112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128029, d163112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128030 q = 1) (hb : d163113 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128030, d163113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128030, d163113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128124 q = 1) (hb : d163173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d163173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128124, d163173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33580 q ha hb
  have h18 (q : Pattern) (ha : d128131 q = 1) (hb : d163184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128131, d163184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128131, d163184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33582 q ha hb
  have h19 (q : Pattern) (ha : d128132 q = 1) (hb : d163185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d163185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128132, d163185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128133 q = 1) (hb : d163186 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d163186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128133, d163186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128134 q = 1) (hb : d163187 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d163187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128134, d163187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128135 q = 1) (hb : d163188 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d163188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128135, d163188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d128136 q = 1) (hb : d163189 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d163189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128136, d163189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro33584 (p : Pattern) (ha : d128142 p = 1) (hb : d163195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d163190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d163190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d163190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33583 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d163191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d163191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d163191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d163192 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d163192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d163192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d163193 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d163193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d163193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d163194 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d163194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d163194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d163195 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d163195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d163195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33585 (p : Pattern) (ha : d128148 p = 1) (hb : d163201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d162312 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d162312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33358 q ha hb
    | true =>
      simp only [d127103, d162312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33389 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d162464 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d162464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d162464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33422 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d162465 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d162465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d162465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d162709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d162709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d162709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33477 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d162710 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d162710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d162710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d162711 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d162711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d162711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d162953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d162953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d162953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33531 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d162954 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d162954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d162954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d162955 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d162955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d162955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d162956 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d162956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d162956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d163196 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d163196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d163196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33584 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d163197 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d163197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d163197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d163198 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d163198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d163198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d163199 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d163199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d163199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d163200 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d163200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d163200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d163201 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d163201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d163201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro33586 (p : Pattern) (ha : d128154 p = 1) (hb : d163207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d163202 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d163202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33585 q ha hb
    | true =>
      simp only [d128149, d163202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d163203 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d163203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d163203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d163204 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d163204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d163204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d163205 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d163205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d163205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d163206 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d163206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d163206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d163207 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d163207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d163207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33587 (p : Pattern) (ha : d128160 p = 1) (hb : d163213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d163208 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d163208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33586 q ha hb
    | true =>
      simp only [d128155, d163208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d163209 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d163209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d163209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d163210 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d163210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d163210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d163211 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d163211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d163211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d163212 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d163212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d163212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d163213 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d163213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d163213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33588 (p : Pattern) (ha : d128166 p = 1) (hb : d163219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d163214 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d163214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33587 q ha hb
    | true =>
      simp only [d128161, d163214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d163215 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d163215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d163215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d163216 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d163216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d163216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d163217 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d163217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d163217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d163218 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d163218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d163218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d163219 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d163219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d163219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33589 (p : Pattern) (ha : d128172 p = 1) (hb : d163225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d163220 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d163220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33588 q ha hb
    | true =>
      simp only [d128167, d163220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d163221 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d163221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d163221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d163222 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d163222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d163222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d163223 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d163223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d163223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d163224 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d163224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d163224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d163225 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d163225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d163225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33590 (p : Pattern) (ha : d128178 p = 1) (hb : d163231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d163226 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d163226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33589 q ha hb
    | true =>
      simp only [d128173, d163226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d163227 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d163227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d163227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d163228 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d163228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d163228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d163229 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d163229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d163229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d163230 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d163230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d163230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d163231 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d163231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d163231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33591 (p : Pattern) (ha : d128184 p = 1) (hb : d163237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d163232 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d163232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33590 q ha hb
    | true =>
      simp only [d128179, d163232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d163233 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d163233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d163233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d163234 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d163234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d163234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d163235 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d163235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d163235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d163236 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d163236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d163236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d163237 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d163237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d163237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33592 (p : Pattern) (ha : d128190 p = 1) (hb : d163243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d163238 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d163238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33591 q ha hb
    | true =>
      simp only [d128185, d163238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d163239 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d163239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d163239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d163240 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d163240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d163240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d163241 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d163241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d163241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d163242 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d163242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d163242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d163243 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d163243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d163243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33593 (p : Pattern) (ha : d150354 p = 1) (hb : d162092 p = 1) : d163246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12462 q = 1) (hb : d162092 q = 1) : d12462 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12463 q = 1) (hb : d162092 q = 1) : d162180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33120 q ha hb
    | true =>
      simp only [d12463, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12464 q = 1) (hb : d162092 q = 1) : d162181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12465 q = 1) (hb : d162092 q = 1) : d162182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12465, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12466 q = 1) (hb : d162092 q = 1) : d162183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12467 q = 1) (hb : d162092 q = 1) : d162184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150354 q = 1) (hb : d162092 q = 1) : d163246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150354, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33594 (p : Pattern) (ha : d150365 p = 1) (hb : d162092 p = 1) : d163257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12668 q = 1) (hb : d162092 q = 1) : d12668 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150360 q = 1) (hb : d162092 q = 1) : d163252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33140 q ha hb
    | true =>
      simp only [d150360, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150361 q = 1) (hb : d162092 q = 1) : d163253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150361, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150362 q = 1) (hb : d162092 q = 1) : d163254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150362, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150363 q = 1) (hb : d162092 q = 1) : d163255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150363, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150364 q = 1) (hb : d162092 q = 1) : d163256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150364, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150365 q = 1) (hb : d162092 q = 1) : d163257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150365, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33595 (p : Pattern) (ha : d150371 p = 1) (hb : d162092 p = 1) : d163263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d162092 q = 1) : d162186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33119 q ha hb
    | true =>
      simp only [d12469, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33121 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d162092 q = 1) : d162187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150352 q = 1) (hb : d162092 q = 1) : d163244 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150352, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150353 q = 1) (hb : d162092 q = 1) : d163245 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150353, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150355 q = 1) (hb : d162092 q = 1) : d163247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150355, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33593 q ha hb
  have h6 (q : Pattern) (ha : d150356 q = 1) (hb : d162092 q = 1) : d163248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150357 q = 1) (hb : d162092 q = 1) : d163249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150358 q = 1) (hb : d162092 q = 1) : d163250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150359 q = 1) (hb : d162092 q = 1) : d163251 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150366 q = 1) (hb : d162092 q = 1) : d163258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150366, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33594 q ha hb
  have h11 (q : Pattern) (ha : d150367 q = 1) (hb : d162092 q = 1) : d163259 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150368 q = 1) (hb : d162092 q = 1) : d163260 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150369 q = 1) (hb : d162092 q = 1) : d163261 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150370 q = 1) (hb : d162092 q = 1) : d163262 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150371 q = 1) (hb : d162092 q = 1) : d163263 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33596 (p : Pattern) (ha : d150377 p = 1) (hb : d162092 p = 1) : d163269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150372 q = 1) (hb : d162092 q = 1) : d163264 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150372, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33595 q ha hb
  have h2 (q : Pattern) (ha : d150373 q = 1) (hb : d162092 q = 1) : d163265 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150373, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150374 q = 1) (hb : d162092 q = 1) : d163266 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150374, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150375 q = 1) (hb : d162092 q = 1) : d163267 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150375, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150376 q = 1) (hb : d162092 q = 1) : d163268 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150376, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150377 q = 1) (hb : d162092 q = 1) : d163269 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150377, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33597 (p : Pattern) (ha : d150381 p = 1) (hb : d162092 p = 1) : d163273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12717 q = 1) (hb : d162092 q = 1) : d12717 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12718 q = 1) (hb : d162092 q = 1) : d162331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33148 q ha hb
    | true =>
      simp only [d12718, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12719 q = 1) (hb : d162092 q = 1) : d162332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12720 q = 1) (hb : d162092 q = 1) : d162333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12720, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12721 q = 1) (hb : d162092 q = 1) : d162334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12722 q = 1) (hb : d162092 q = 1) : d162335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150381 q = 1) (hb : d162092 q = 1) : d163273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150381, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33598 (p : Pattern) (ha : d150392 p = 1) (hb : d162092 p = 1) : d163284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12935 q = 1) (hb : d162092 q = 1) : d12935 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150387 q = 1) (hb : d162092 q = 1) : d163279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33168 q ha hb
    | true =>
      simp only [d150387, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150388 q = 1) (hb : d162092 q = 1) : d163280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150388, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150389 q = 1) (hb : d162092 q = 1) : d163281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150389, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150390 q = 1) (hb : d162092 q = 1) : d163282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150390, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150391 q = 1) (hb : d162092 q = 1) : d163283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150391, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150392 q = 1) (hb : d162092 q = 1) : d163284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150392, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33599 (p : Pattern) (ha : d150398 p = 1) (hb : d162092 p = 1) : d163290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d162092 q = 1) : d162337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33147 q ha hb
    | true =>
      simp only [d12724, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33149 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d162092 q = 1) : d162338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150379 q = 1) (hb : d162092 q = 1) : d163271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150379, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150380 q = 1) (hb : d162092 q = 1) : d163272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150380, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150382 q = 1) (hb : d162092 q = 1) : d163274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150382, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33597 q ha hb
  have h6 (q : Pattern) (ha : d150383 q = 1) (hb : d162092 q = 1) : d163275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150384 q = 1) (hb : d162092 q = 1) : d163276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150385 q = 1) (hb : d162092 q = 1) : d163277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150386 q = 1) (hb : d162092 q = 1) : d163278 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150393 q = 1) (hb : d162092 q = 1) : d163285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150393, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33598 q ha hb
  have h11 (q : Pattern) (ha : d150394 q = 1) (hb : d162092 q = 1) : d163286 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150395 q = 1) (hb : d162092 q = 1) : d163287 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150396 q = 1) (hb : d162092 q = 1) : d163288 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150397 q = 1) (hb : d162092 q = 1) : d163289 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150398 q = 1) (hb : d162092 q = 1) : d163290 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33600 (p : Pattern) (ha : d150404 p = 1) (hb : d162092 p = 1) : d163296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150399 q = 1) (hb : d162092 q = 1) : d163291 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150399, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33599 q ha hb
  have h2 (q : Pattern) (ha : d150400 q = 1) (hb : d162092 q = 1) : d163292 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150400, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150401 q = 1) (hb : d162092 q = 1) : d163293 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150401, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150402 q = 1) (hb : d162092 q = 1) : d163294 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150402, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150403 q = 1) (hb : d162092 q = 1) : d163295 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150403, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150404 q = 1) (hb : d162092 q = 1) : d163296 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150404, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33601 (p : Pattern) (ha : d150409 p = 1) (hb : d162092 p = 1) : d163301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d162092 q = 1) : d162507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33180 q ha hb
    | true =>
      simp only [d12992, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33181 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d162092 q = 1) : d162508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d162092 q = 1) : d162509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d162092 q = 1) : d162510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d162092 q = 1) : d162511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150409 q = 1) (hb : d162092 q = 1) : d163301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150409, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33602 (p : Pattern) (ha : d150418 p = 1) (hb : d162092 p = 1) : d163310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d162092 q = 1) : d162674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33216 q ha hb
    | true =>
      simp only [d13244, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d162092 q = 1) : d162675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d162092 q = 1) : d162664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33189 q ha hb
    | true =>
      simp only [d13197, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d162092 q = 1) : d162665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150415 q = 1) (hb : d162092 q = 1) : d163307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150415, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150416 q = 1) (hb : d162092 q = 1) : d163308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150417 q = 1) (hb : d162092 q = 1) : d163309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150418 q = 1) (hb : d162092 q = 1) : d163310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33603 (p : Pattern) (ha : d150424 p = 1) (hb : d162092 p = 1) : d163316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150419 q = 1) (hb : d162092 q = 1) : d163311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33602 q ha hb
    | true =>
      simp only [d150419, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33190 q ha hb
  have h2 (q : Pattern) (ha : d150420 q = 1) (hb : d162092 q = 1) : d163312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150420, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150421 q = 1) (hb : d162092 q = 1) : d163313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150422 q = 1) (hb : d162092 q = 1) : d163314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150422, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150423 q = 1) (hb : d162092 q = 1) : d163315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150423, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150424 q = 1) (hb : d162092 q = 1) : d163316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150424, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33604 (p : Pattern) (ha : d150430 p = 1) (hb : d162092 p = 1) : d163322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d162092 q = 1) : d162513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33179 q ha hb
    | true =>
      simp only [d12998, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33182 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d162092 q = 1) : d162514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150407 q = 1) (hb : d162092 q = 1) : d163299 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150407, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150408 q = 1) (hb : d162092 q = 1) : d163300 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150408, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150410 q = 1) (hb : d162092 q = 1) : d163302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150410, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33601 q ha hb
  have h6 (q : Pattern) (ha : d150411 q = 1) (hb : d162092 q = 1) : d163303 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150412 q = 1) (hb : d162092 q = 1) : d163304 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150413 q = 1) (hb : d162092 q = 1) : d163305 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150414 q = 1) (hb : d162092 q = 1) : d163306 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150425 q = 1) (hb : d162092 q = 1) : d163317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150425, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33603 q ha hb
  have h11 (q : Pattern) (ha : d150426 q = 1) (hb : d162092 q = 1) : d163318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150427 q = 1) (hb : d162092 q = 1) : d163319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150428 q = 1) (hb : d162092 q = 1) : d163320 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150429 q = 1) (hb : d162092 q = 1) : d163321 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150430 q = 1) (hb : d162092 q = 1) : d163322 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33605 (p : Pattern) (ha : d150436 p = 1) (hb : d162092 p = 1) : d163328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150431 q = 1) (hb : d162092 q = 1) : d163323 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150431, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33604 q ha hb
  have h2 (q : Pattern) (ha : d150432 q = 1) (hb : d162092 q = 1) : d163324 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150432, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150433 q = 1) (hb : d162092 q = 1) : d163325 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150433, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150434 q = 1) (hb : d162092 q = 1) : d163326 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150434, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150435 q = 1) (hb : d162092 q = 1) : d163327 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150435, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150436 q = 1) (hb : d162092 q = 1) : d163328 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150436, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33606 (p : Pattern) (ha : d150442 p = 1) (hb : d162092 p = 1) : d163334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d162092 q = 1) : d162753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33228 q ha hb
    | true =>
      simp only [d13318, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33229 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d162092 q = 1) : d162754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d162092 q = 1) : d162755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d162092 q = 1) : d162756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d162092 q = 1) : d162757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150442 q = 1) (hb : d162092 q = 1) : d163334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150442, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33607 (p : Pattern) (ha : d150451 p = 1) (hb : d162092 p = 1) : d163343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d162092 q = 1) : d162918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33264 q ha hb
    | true =>
      simp only [d13570, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d162092 q = 1) : d162919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d162092 q = 1) : d162908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33237 q ha hb
    | true =>
      simp only [d13523, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d162092 q = 1) : d162909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150448 q = 1) (hb : d162092 q = 1) : d163340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150448, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150449 q = 1) (hb : d162092 q = 1) : d163341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150450 q = 1) (hb : d162092 q = 1) : d163342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150451 q = 1) (hb : d162092 q = 1) : d163343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33608 (p : Pattern) (ha : d150457 p = 1) (hb : d162092 p = 1) : d163349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150452 q = 1) (hb : d162092 q = 1) : d163344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33607 q ha hb
    | true =>
      simp only [d150452, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33238 q ha hb
  have h2 (q : Pattern) (ha : d150453 q = 1) (hb : d162092 q = 1) : d163345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150453, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150454 q = 1) (hb : d162092 q = 1) : d163346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150455 q = 1) (hb : d162092 q = 1) : d163347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150455, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150456 q = 1) (hb : d162092 q = 1) : d163348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150456, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150457 q = 1) (hb : d162092 q = 1) : d163349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150457, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33609 (p : Pattern) (ha : d150463 p = 1) (hb : d162092 p = 1) : d163355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d162092 q = 1) : d162759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33227 q ha hb
    | true =>
      simp only [d13324, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33230 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d162092 q = 1) : d162760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150440 q = 1) (hb : d162092 q = 1) : d163332 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150440, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150441 q = 1) (hb : d162092 q = 1) : d163333 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150441, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150443 q = 1) (hb : d162092 q = 1) : d163335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150443, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33606 q ha hb
  have h6 (q : Pattern) (ha : d150444 q = 1) (hb : d162092 q = 1) : d163336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150445 q = 1) (hb : d162092 q = 1) : d163337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150446 q = 1) (hb : d162092 q = 1) : d163338 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150447 q = 1) (hb : d162092 q = 1) : d163339 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150458 q = 1) (hb : d162092 q = 1) : d163350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150458, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33608 q ha hb
  have h11 (q : Pattern) (ha : d150459 q = 1) (hb : d162092 q = 1) : d163351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150460 q = 1) (hb : d162092 q = 1) : d163352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150461 q = 1) (hb : d162092 q = 1) : d163353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150462 q = 1) (hb : d162092 q = 1) : d163354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150463 q = 1) (hb : d162092 q = 1) : d163355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33610 (p : Pattern) (ha : d150469 p = 1) (hb : d162092 p = 1) : d163361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150464 q = 1) (hb : d162092 q = 1) : d163356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150464, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33609 q ha hb
  have h2 (q : Pattern) (ha : d150465 q = 1) (hb : d162092 q = 1) : d163357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150465, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150466 q = 1) (hb : d162092 q = 1) : d163358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150466, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150467 q = 1) (hb : d162092 q = 1) : d163359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150467, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150468 q = 1) (hb : d162092 q = 1) : d163360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150468, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150469 q = 1) (hb : d162092 q = 1) : d163361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150469, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33611 (p : Pattern) (ha : d150476 p = 1) (hb : d162092 p = 1) : d163368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d162092 q = 1) : d162997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33276 q ha hb
    | true =>
      simp only [d13645, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33277 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d162092 q = 1) : d162998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d162092 q = 1) : d162999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d162092 q = 1) : d163000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d162092 q = 1) : d163001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150476 q = 1) (hb : d162092 q = 1) : d163368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150476, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33612 (p : Pattern) (ha : d150485 p = 1) (hb : d162092 p = 1) : d163377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d162092 q = 1) : d163161 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33312 q ha hb
    | true =>
      simp only [d13897, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d162092 q = 1) : d163162 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d162092 q = 1) : d163151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33285 q ha hb
    | true =>
      simp only [d13850, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d162092 q = 1) : d163152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150482 q = 1) (hb : d162092 q = 1) : d163374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150482, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150483 q = 1) (hb : d162092 q = 1) : d163375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150484 q = 1) (hb : d162092 q = 1) : d163376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150485 q = 1) (hb : d162092 q = 1) : d163377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33613 (p : Pattern) (ha : d150491 p = 1) (hb : d162092 p = 1) : d163383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150486 q = 1) (hb : d162092 q = 1) : d163378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33612 q ha hb
    | true =>
      simp only [d150486, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33286 q ha hb
  have h2 (q : Pattern) (ha : d150487 q = 1) (hb : d162092 q = 1) : d163379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150487, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150488 q = 1) (hb : d162092 q = 1) : d163380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150489 q = 1) (hb : d162092 q = 1) : d163381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150489, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150490 q = 1) (hb : d162092 q = 1) : d163382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150490, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150491 q = 1) (hb : d162092 q = 1) : d163383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150491, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33614 (p : Pattern) (ha : d150497 p = 1) (hb : d162092 p = 1) : d163389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d162092 q = 1) : d163003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33275 q ha hb
    | true =>
      simp only [d13651, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33278 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d162092 q = 1) : d163004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150474 q = 1) (hb : d162092 q = 1) : d163366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150474, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150475 q = 1) (hb : d162092 q = 1) : d163367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150475, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150477 q = 1) (hb : d162092 q = 1) : d163369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150477, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33611 q ha hb
  have h6 (q : Pattern) (ha : d150478 q = 1) (hb : d162092 q = 1) : d163370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150479 q = 1) (hb : d162092 q = 1) : d163371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150480 q = 1) (hb : d162092 q = 1) : d163372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150481 q = 1) (hb : d162092 q = 1) : d163373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150492 q = 1) (hb : d162092 q = 1) : d163384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150492, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33613 q ha hb
  have h11 (q : Pattern) (ha : d150493 q = 1) (hb : d162092 q = 1) : d163385 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150494 q = 1) (hb : d162092 q = 1) : d163386 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150495 q = 1) (hb : d162092 q = 1) : d163387 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150496 q = 1) (hb : d162092 q = 1) : d163388 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150497 q = 1) (hb : d162092 q = 1) : d163389 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33615 (p : Pattern) (ha : d150503 p = 1) (hb : d162092 p = 1) : d163395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150498 q = 1) (hb : d162092 q = 1) : d163390 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150498, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33614 q ha hb
  have h2 (q : Pattern) (ha : d150499 q = 1) (hb : d162092 q = 1) : d163391 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150499, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150500 q = 1) (hb : d162092 q = 1) : d163392 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150500, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150501 q = 1) (hb : d162092 q = 1) : d163393 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150501, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150502 q = 1) (hb : d162092 q = 1) : d163394 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150502, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150503 q = 1) (hb : d162092 q = 1) : d163395 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150503, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33616 (p : Pattern) (ha : d150509 p = 1) (hb : d162092 p = 1) : d163401 p = 1 := by
  have h0 (q : Pattern) (ha : d150351 q = 1) (hb : d162092 q = 1) : d150351 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150378 q = 1) (hb : d162092 q = 1) : d163270 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150378, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33596 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150405 q = 1) (hb : d162092 q = 1) : d163297 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150405, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33600 q ha hb
  have h4 (q : Pattern) (ha : d150406 q = 1) (hb : d162092 q = 1) : d163298 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150406, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150437 q = 1) (hb : d162092 q = 1) : d163329 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150437, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33605 q ha hb
  have h6 (q : Pattern) (ha : d150438 q = 1) (hb : d162092 q = 1) : d163330 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150438, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150439 q = 1) (hb : d162092 q = 1) : d163331 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150439, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150470 q = 1) (hb : d162092 q = 1) : d163362 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150470, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33610 q ha hb
  have h9 (q : Pattern) (ha : d150471 q = 1) (hb : d162092 q = 1) : d163363 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150471, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150472 q = 1) (hb : d162092 q = 1) : d163364 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150472, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150473 q = 1) (hb : d162092 q = 1) : d163365 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150473, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150504 q = 1) (hb : d162092 q = 1) : d163396 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150504, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33615 q ha hb
  have h13 (q : Pattern) (ha : d150505 q = 1) (hb : d162092 q = 1) : d163397 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150505, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150506 q = 1) (hb : d162092 q = 1) : d163398 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150506, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150507 q = 1) (hb : d162092 q = 1) : d163399 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150507, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150508 q = 1) (hb : d162092 q = 1) : d163400 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150508, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150509 q = 1) (hb : d162092 q = 1) : d163401 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150509, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h17 p ha hb
theorem andIntro33617 (p : Pattern) (ha : d150515 p = 1) (hb : d162092 p = 1) : d163407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150510 q = 1) (hb : d162092 q = 1) : d163402 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33616 q ha hb
    | true =>
      simp only [d150510, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150511 q = 1) (hb : d162092 q = 1) : d163403 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150512 q = 1) (hb : d162092 q = 1) : d163404 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150513 q = 1) (hb : d162092 q = 1) : d163405 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150514 q = 1) (hb : d162092 q = 1) : d163406 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150515 q = 1) (hb : d162092 q = 1) : d163407 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33618 (p : Pattern) (ha : d150521 p = 1) (hb : d162092 p = 1) : d163413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150516 q = 1) (hb : d162092 q = 1) : d163408 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33617 q ha hb
    | true =>
      simp only [d150516, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150517 q = 1) (hb : d162092 q = 1) : d163409 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150518 q = 1) (hb : d162092 q = 1) : d163410 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150519 q = 1) (hb : d162092 q = 1) : d163411 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150520 q = 1) (hb : d162092 q = 1) : d163412 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150521 q = 1) (hb : d162092 q = 1) : d163413 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33619 (p : Pattern) (ha : d150527 p = 1) (hb : d162095 p = 1) : d163419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150522 q = 1) (hb : d162092 q = 1) : d163414 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33618 q ha hb
    | true =>
      simp only [d150522, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150523 q = 1) (hb : d162092 q = 1) : d163415 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150524 q = 1) (hb : d162092 q = 1) : d163416 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150525 q = 1) (hb : d162092 q = 1) : d163417 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150526 q = 1) (hb : d162092 q = 1) : d163418 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150527 q = 1) (hb : d162095 q = 1) : d163419 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d162095, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d162095, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33620 (p : Pattern) (ha : d150533 p = 1) (hb : d162095 p = 1) : d163425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150528 q = 1) (hb : d162095 q = 1) : d163420 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33619 q ha hb
    | true =>
      simp only [d150528, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150529 q = 1) (hb : d162095 q = 1) : d163421 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150530 q = 1) (hb : d162095 q = 1) : d163422 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150531 q = 1) (hb : d162095 q = 1) : d163423 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150532 q = 1) (hb : d162095 q = 1) : d163424 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150533 q = 1) (hb : d162095 q = 1) : d163425 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33621 (p : Pattern) (ha : d150539 p = 1) (hb : d162095 p = 1) : d163431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150534 q = 1) (hb : d162095 q = 1) : d163426 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33620 q ha hb
    | true =>
      simp only [d150534, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150535 q = 1) (hb : d162095 q = 1) : d163427 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150536 q = 1) (hb : d162095 q = 1) : d163428 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150537 q = 1) (hb : d162095 q = 1) : d163429 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150538 q = 1) (hb : d162095 q = 1) : d163430 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150539 q = 1) (hb : d162095 q = 1) : d163431 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33622 (p : Pattern) (ha : d150545 p = 1) (hb : d162095 p = 1) : d163437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150540 q = 1) (hb : d162095 q = 1) : d163432 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33621 q ha hb
    | true =>
      simp only [d150540, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150541 q = 1) (hb : d162095 q = 1) : d163433 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150542 q = 1) (hb : d162095 q = 1) : d163434 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150543 q = 1) (hb : d162095 q = 1) : d163435 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150544 q = 1) (hb : d162095 q = 1) : d163436 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150545 q = 1) (hb : d162095 q = 1) : d163437 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33623 (p : Pattern) (ha : d150551 p = 1) (hb : d162095 p = 1) : d163443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150546 q = 1) (hb : d162095 q = 1) : d163438 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33622 q ha hb
    | true =>
      simp only [d150546, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150547 q = 1) (hb : d162095 q = 1) : d163439 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150548 q = 1) (hb : d162095 q = 1) : d163440 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150549 q = 1) (hb : d162095 q = 1) : d163441 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150550 q = 1) (hb : d162095 q = 1) : d163442 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150551 q = 1) (hb : d162095 q = 1) : d163443 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33624 (p : Pattern) (ha : d12289 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12234 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33326 q ha hb
    | true =>
      simp only [d12234, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d12285 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12285, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12286 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12286, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12287 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12287, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12288 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12288, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12289 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33625 (p : Pattern) (ha : d12296 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12234 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33326 q ha hb
    | true =>
      simp only [d12234, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d12285 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12285, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12286 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12286, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12287 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12287, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12288 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12241 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33328 q ha hb
    | true =>
      simp only [d12241, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d12292 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12292, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12293 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12293, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12294 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12294, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12295 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12295, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12296 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12296, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33626 (p : Pattern) (ha : d126906 p = 1) (hb : d150329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33328 q ha hb
    | true =>
      simp only [d12241, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12292, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12293 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12294 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12295 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126906 q = 1) (hb : d150329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro33627 (p : Pattern) (ha : d126930 p = 1) (hb : d150339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33332 q ha hb
    | true =>
      simp only [d12268, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d150335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126927 q = 1) (hb : d150336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126928 q = 1) (hb : d150337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126929 q = 1) (hb : d150338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126930 q = 1) (hb : d150339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33628 (p : Pattern) (ha : d126936 p = 1) (hb : d150345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d126900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33624 q ha hb
    | true =>
      simp only [d12297, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33625 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12298 q = 1) (hb : d126901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126902 q = 1) (hb : d150327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126902, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d126902, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126903 q = 1) (hb : d150328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126903, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126903, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126907 q = 1) (hb : d150330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126907, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126907, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33626 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d126908 q = 1) (hb : d150331 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126908, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126908, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d126909 q = 1) (hb : d150332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126909, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126909, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d126910 q = 1) (hb : d150333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126910, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126910, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d126911 q = 1) (hb : d150334 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126911, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126911, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126931 q = 1) (hb : d150340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126931, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33627 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d126932 q = 1) (hb : d150341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126932, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d126933 q = 1) (hb : d150342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126933, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d126934 q = 1) (hb : d150343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d126934, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d126935 q = 1) (hb : d150344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d126935, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d126936 q = 1) (hb : d150345 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d126936, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33629 (p : Pattern) (ha : d126942 p = 1) (hb : d150351 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d126937 q = 1) (hb : d150346 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126937, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33628 q ha hb
  have h8 (q : Pattern) (ha : d126938 q = 1) (hb : d150347 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126938, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126939 q = 1) (hb : d150348 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126939, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126940 q = 1) (hb : d150349 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126940, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d126941 q = 1) (hb : d150350 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126941, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126942 q = 1) (hb : d150351 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126942, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro33630 (p : Pattern) (ha : d127013 p = 1) (hb : d162176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d126951 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126951, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33360 q ha hb
    | true =>
      simp only [d126951, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h5 (q : Pattern) (ha : d127003 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127003, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127003, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d127010 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127010, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127010, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d127011 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127011, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127011, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127012 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127012, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127012, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127013 q = 1) (hb : d162176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127013, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127013, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33631 (p : Pattern) (ha : d127032 p = 1) (hb : d162185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d126951 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126951, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33360 q ha hb
    | true =>
      simp only [d126951, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h4 (q : Pattern) (ha : d127003 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127003, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127003, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d127010 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127010, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127010, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127011 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127011, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127011, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127012 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127012, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127012, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d126960 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126960, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33362 q ha hb
    | true =>
      simp only [d126960, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q hb ha
  have h13 (q : Pattern) (ha : d127025 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127025, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d127025, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127029 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127029, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127029, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127030 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127030, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d127030, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d127031 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127031, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127031, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127032 q = 1) (hb : d162185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127032, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127032, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33632 (p : Pattern) (ha : d127041 p = 1) (hb : d163246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126960 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126960, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33362 q ha hb
    | true =>
      simp only [d126960, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q hb ha
  have h3 (q : Pattern) (ha : d127025 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127025, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127025, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127029 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127029, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127029, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127039 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127039, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127039, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127040 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127040, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127040, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127041 q = 1) (hb : d163246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127041, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127041, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33633 (p : Pattern) (ha : d127090 p = 1) (hb : d163257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d163252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33385 q ha hb
    | true =>
      simp only [d127079, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28709 q hb ha
  have h3 (q : Pattern) (ha : d127080 q = 1) (hb : d163253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127080, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127080, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127087 q = 1) (hb : d163254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127087, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127087, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127088 q = 1) (hb : d163255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127088, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127088, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127089 q = 1) (hb : d163256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127089, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127089, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127090 q = 1) (hb : d163257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127090, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127090, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33634 (p : Pattern) (ha : d127096 p = 1) (hb : d163263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127033 q = 1) (hb : d162186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127033, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33630 q ha hb
    | true =>
      simp only [d127033, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33631 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127036 q = 1) (hb : d162187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127036, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127036, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127037 q = 1) (hb : d163244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127037, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127037, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127038 q = 1) (hb : d163245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127038, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127038, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127042 q = 1) (hb : d163247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127042, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127042, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33632 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127043 q = 1) (hb : d163248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127043, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127043, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127044 q = 1) (hb : d163249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127044, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127044, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127045 q = 1) (hb : d163250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127045, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127045, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127046 q = 1) (hb : d163251 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127046, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127046, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127091 q = 1) (hb : d163258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127091, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127091, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33633 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127092 q = 1) (hb : d163259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127092, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127092, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127093 q = 1) (hb : d163260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127093, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127093, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127094 q = 1) (hb : d163261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127094, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127094, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127095 q = 1) (hb : d163262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127095, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127095, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127096 q = 1) (hb : d163263 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127096, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127096, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33635 (p : Pattern) (ha : d127102 p = 1) (hb : d163269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127097 q = 1) (hb : d163264 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127097, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127097, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33634 q ha hb
  have h2 (q : Pattern) (ha : d127098 q = 1) (hb : d163265 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127098, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127098, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127099 q = 1) (hb : d163266 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127099, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127099, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127100 q = 1) (hb : d163267 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127100, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127100, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127101 q = 1) (hb : d163268 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127101, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127101, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127102 q = 1) (hb : d163269 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127102, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127102, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33636 (p : Pattern) (ha : d127179 p = 1) (hb : d162327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127117 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127117, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33392 q ha hb
    | true =>
      simp only [d127117, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h5 (q : Pattern) (ha : d127169 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127169, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127169, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d127176 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127176, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127176, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d127177 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127177, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127177, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127178 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127178, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127178, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127179 q = 1) (hb : d162327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127179, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127179, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33637 (p : Pattern) (ha : d127198 p = 1) (hb : d162336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127117 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127117, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33392 q ha hb
    | true =>
      simp only [d127117, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h4 (q : Pattern) (ha : d127169 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127169, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127169, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d127176 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127176, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127176, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127177 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127177, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127177, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127178 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127178, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127178, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127184 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d127126 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127126, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33394 q ha hb
    | true =>
      simp only [d127126, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q hb ha
  have h13 (q : Pattern) (ha : d127191 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127191, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d127191, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127195 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127195, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127195, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127196 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127196, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d127196, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d127197 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127197, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127197, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127198 q = 1) (hb : d162336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127198, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127198, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33638 (p : Pattern) (ha : d127207 p = 1) (hb : d163273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127126 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127126, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33394 q ha hb
    | true =>
      simp only [d127126, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q hb ha
  have h3 (q : Pattern) (ha : d127191 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127191, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127191, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127195 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127195, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127195, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127205 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127205, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127205, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127206 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127206, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127206, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127207 q = 1) (hb : d163273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127207, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127207, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33639 (p : Pattern) (ha : d127261 p = 1) (hb : d163284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127250 q = 1) (hb : d163279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127250, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33418 q ha hb
    | true =>
      simp only [d127250, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28751 q hb ha
  have h3 (q : Pattern) (ha : d127251 q = 1) (hb : d163280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127251, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127251, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127257 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127258 q = 1) (hb : d163281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127258, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127258, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127259 q = 1) (hb : d163282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127259, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127259, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127260 q = 1) (hb : d163283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127260, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127260, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127261 q = 1) (hb : d163284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127261, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127261, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33640 (p : Pattern) (ha : d127267 p = 1) (hb : d163290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127199 q = 1) (hb : d162337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127199, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33636 q ha hb
    | true =>
      simp only [d127199, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33637 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127202 q = 1) (hb : d162338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127202, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127202, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127203 q = 1) (hb : d163271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127203, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127203, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127204 q = 1) (hb : d163272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127204, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127204, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127208 q = 1) (hb : d163274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127208, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127208, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33638 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127209 q = 1) (hb : d163275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127209, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127209, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127210 q = 1) (hb : d163276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127210, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127210, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127211 q = 1) (hb : d163277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127211, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127211, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127212 q = 1) (hb : d163278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127212, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127212, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127262 q = 1) (hb : d163285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127262, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127262, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33639 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127263 q = 1) (hb : d163286 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127263, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127263, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127264 q = 1) (hb : d163287 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127264, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127264, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127265 q = 1) (hb : d163288 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127265, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127265, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127266 q = 1) (hb : d163289 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127266, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127266, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127267 q = 1) (hb : d163290 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127267, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127267, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33641 (p : Pattern) (ha : d127273 p = 1) (hb : d163296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127268 q = 1) (hb : d163291 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127268, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127268, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33640 q ha hb
  have h2 (q : Pattern) (ha : d127269 q = 1) (hb : d163292 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127269, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127269, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127270 q = 1) (hb : d163293 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127270, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127270, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127271 q = 1) (hb : d163294 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127271, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127271, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127272 q = 1) (hb : d163295 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127272, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127272, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127273 q = 1) (hb : d163296 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127273, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127273, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33642 (p : Pattern) (ha : d127395 p = 1) (hb : d162502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127309 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127309, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33429 q ha hb
    | true =>
      simp only [d127309, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33430 q ha hb
  have h5 (q : Pattern) (ha : d127377 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127377, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127377, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d127392 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127392, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127392, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d127393 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127393, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127393, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127394 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127394, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127394, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127395 q = 1) (hb : d162502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127395, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127395, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33643 (p : Pattern) (ha : d127417 p = 1) (hb : d162512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127309 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127309, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33429 q ha hb
    | true =>
      simp only [d127309, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33430 q ha hb
  have h4 (q : Pattern) (ha : d127377 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127377, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127377, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d127392 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127392, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127392, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127393 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127393, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127393, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127394 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127394, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127394, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d127319 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127319, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33432 q ha hb
    | true =>
      simp only [d127319, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33433 q ha hb
  have h13 (q : Pattern) (ha : d127410 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127410, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d127410, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127414 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127414, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127414, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127415 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127415, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d127415, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d127416 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127416, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127416, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127417 q = 1) (hb : d162512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127417, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127417, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33644 (p : Pattern) (ha : d127442 p = 1) (hb : d163301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127319 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127319, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33432 q ha hb
    | true =>
      simp only [d127319, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33433 q ha hb
  have h3 (q : Pattern) (ha : d127410 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127410, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127410, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127414 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127414, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127414, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127440 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127440, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127440, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127441 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127441, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127441, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127442 q = 1) (hb : d163301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127442, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127442, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33645 (p : Pattern) (ha : d127508 p = 1) (hb : d162673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127474 q = 1) (hb : d162638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127474, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33464 q ha hb
    | true =>
      simp only [d127474, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33465 q ha hb
  have h2 (q : Pattern) (ha : d127475 q = 1) (hb : d162639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127475, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127475, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127476 q = 1) (hb : d162640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127476, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127476, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127477 q = 1) (hb : d162641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127477, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33465 q ha hb
    | true =>
      simp only [d127477, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22285 q hb ha
  have h5 (q : Pattern) (ha : d127478 q = 1) (hb : d162642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127478, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127478, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127479 q = 1) (hb : d162643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127479, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127479, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127480 q = 1) (hb : d162644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127480, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127480, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127494 q = 1) (hb : d162658 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127494, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33465 q ha hb
    | true =>
      simp only [d127494, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22288 q hb ha
  have h9 (q : Pattern) (ha : d127495 q = 1) (hb : d162659 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127495, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127495, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127496 q = 1) (hb : d162660 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127496, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127496, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127497 q = 1) (hb : d162661 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127497, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127497, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127507 q = 1) (hb : d162672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127507, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127507, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127508 q = 1) (hb : d162673 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127508, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127508, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33646 (p : Pattern) (ha : d127514 p = 1) (hb : d163310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127509 q = 1) (hb : d162674 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127509, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33645 q ha hb
    | true =>
      simp only [d127509, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127510 q = 1) (hb : d162675 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127510, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127510, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127500 q = 1) (hb : d162664 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127500, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33469 q ha hb
    | true =>
      simp only [d127500, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127501 q = 1) (hb : d162665 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127501, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127501, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127511 q = 1) (hb : d163307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127511, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127511, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127512 q = 1) (hb : d163308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127512, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127512, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127513 q = 1) (hb : d163309 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127513, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127513, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127514 q = 1) (hb : d163310 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127514, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127514, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33647 (p : Pattern) (ha : d127538 p = 1) (hb : d163316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127519 q = 1) (hb : d163311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127519, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33646 q ha hb
    | true =>
      simp only [d127519, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33474 q ha hb
  have h3 (q : Pattern) (ha : d127520 q = 1) (hb : d163312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127520, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127520, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127535 q = 1) (hb : d163313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127535, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127535, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127536 q = 1) (hb : d163314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127536, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127536, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127537 q = 1) (hb : d163315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127537, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127537, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127538 q = 1) (hb : d163316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127538, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127538, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33648 (p : Pattern) (ha : d127551 p = 1) (hb : d163322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127327 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127418 q = 1) (hb : d162513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127418, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33642 q ha hb
    | true =>
      simp only [d127418, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33643 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127437 q = 1) (hb : d162514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127437, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127437, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127438 q = 1) (hb : d163299 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127438, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127438, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127439 q = 1) (hb : d163300 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127439, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127439, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127443 q = 1) (hb : d163302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127443, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127443, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33644 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127445 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127446 q = 1) (hb : d163303 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127446, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127446, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127447 q = 1) (hb : d163304 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127447, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127447, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127448 q = 1) (hb : d163305 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127448, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127448, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127449 q = 1) (hb : d163306 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127449, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127449, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127539 q = 1) (hb : d163317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127539, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127539, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33647 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127546 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127547 q = 1) (hb : d163318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127547, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127547, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127548 q = 1) (hb : d163319 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127548, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127548, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127549 q = 1) (hb : d163320 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127549, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127549, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127550 q = 1) (hb : d163321 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127550, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127550, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127551 q = 1) (hb : d163322 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127551, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127551, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33649 (p : Pattern) (ha : d127557 p = 1) (hb : d163328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127552 q = 1) (hb : d163323 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127552, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127552, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33648 q ha hb
  have h2 (q : Pattern) (ha : d127553 q = 1) (hb : d163324 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127553, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127553, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127554 q = 1) (hb : d163325 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127554, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127554, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127555 q = 1) (hb : d163326 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127555, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127555, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127556 q = 1) (hb : d163327 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127556, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127556, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127557 q = 1) (hb : d163328 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127557, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127557, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33650 (p : Pattern) (ha : d127683 p = 1) (hb : d162748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127664 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127597 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127597, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33484 q ha hb
    | true =>
      simp only [d127597, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33485 q ha hb
  have h5 (q : Pattern) (ha : d127665 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127665, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127665, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127679 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d127680 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127680, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127680, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d127681 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127681, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127681, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127682 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127682, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127682, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127683 q = 1) (hb : d162748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127683, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127683, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33651 (p : Pattern) (ha : d127705 p = 1) (hb : d162758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127623 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127632 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127597 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127597, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33484 q ha hb
    | true =>
      simp only [d127597, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33485 q ha hb
  have h4 (q : Pattern) (ha : d127665 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127665, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127665, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127679 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d127680 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127680, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127680, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127681 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127681, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127681, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127682 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127682, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127682, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127697 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d127607 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127607, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33487 q ha hb
    | true =>
      simp only [d127607, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33488 q ha hb
  have h13 (q : Pattern) (ha : d127698 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127698, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d127698, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127701 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127702 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127702, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127702, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127703 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127703, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d127703, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d127704 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127704, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127704, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127705 q = 1) (hb : d162758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127705, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127705, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33652 (p : Pattern) (ha : d127730 p = 1) (hb : d163334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127607 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127607, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33487 q ha hb
    | true =>
      simp only [d127607, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33488 q ha hb
  have h3 (q : Pattern) (ha : d127698 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127698, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127698, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127701 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127702 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127702, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127702, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127728 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127728, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127728, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127729 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127729, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127729, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127730 q = 1) (hb : d163334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127730, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127730, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33653 (p : Pattern) (ha : d127801 p = 1) (hb : d162917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127767 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33518 q ha hb
    | true =>
      simp only [d127767, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
  have h2 (q : Pattern) (ha : d127768 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127769 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127770 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127770, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22338 q hb ha
  have h5 (q : Pattern) (ha : d127771 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127772 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127773 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127773, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127787 q = 1) (hb : d162902 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127787, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33519 q ha hb
    | true =>
      simp only [d127787, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22341 q hb ha
  have h9 (q : Pattern) (ha : d127788 q = 1) (hb : d162903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127788, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127788, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127789 q = 1) (hb : d162904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127789, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127789, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127790 q = 1) (hb : d162905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127790, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127790, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127800 q = 1) (hb : d162916 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127800, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127800, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127801 q = 1) (hb : d162917 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127801, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127801, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33654 (p : Pattern) (ha : d127807 p = 1) (hb : d163343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127802 q = 1) (hb : d162918 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127802, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33653 q ha hb
    | true =>
      simp only [d127802, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127803 q = 1) (hb : d162919 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127803, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127803, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127793 q = 1) (hb : d162908 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127793, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33523 q ha hb
    | true =>
      simp only [d127793, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d127794 q = 1) (hb : d162909 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127794, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127794, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127804 q = 1) (hb : d163340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127804, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127804, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127805 q = 1) (hb : d163341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127805, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127805, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127806 q = 1) (hb : d163342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127806, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127806, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127807 q = 1) (hb : d163343 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127807, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127807, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33655 (p : Pattern) (ha : d127831 p = 1) (hb : d163349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127799 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127812 q = 1) (hb : d163344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127812, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33654 q ha hb
    | true =>
      simp only [d127812, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33528 q ha hb
  have h3 (q : Pattern) (ha : d127813 q = 1) (hb : d163345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127813, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127813, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127828 q = 1) (hb : d163346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127828, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127828, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127829 q = 1) (hb : d163347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127829, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127829, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127830 q = 1) (hb : d163348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127830, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127830, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127831 q = 1) (hb : d163349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127831, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127831, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33656 (p : Pattern) (ha : d127844 p = 1) (hb : d163355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127706 q = 1) (hb : d162759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127706, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33650 q ha hb
    | true =>
      simp only [d127706, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33651 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127725 q = 1) (hb : d162760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127725, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d127725, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127726 q = 1) (hb : d163332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127726, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127726, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127727 q = 1) (hb : d163333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127727, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127727, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127731 q = 1) (hb : d163335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127731, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127731, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33652 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127733 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127734 q = 1) (hb : d163336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127734, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127734, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127735 q = 1) (hb : d163337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127735, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127735, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127736 q = 1) (hb : d163338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127736, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127736, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127737 q = 1) (hb : d163339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127737, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127737, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127832 q = 1) (hb : d163350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127832, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127832, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33655 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127839 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127840 q = 1) (hb : d163351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127840, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127840, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127841 q = 1) (hb : d163352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127841, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127841, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127842 q = 1) (hb : d163353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127842, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127842, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127843 q = 1) (hb : d163354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127843, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127843, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127844 q = 1) (hb : d163355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127844, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127844, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33657 (p : Pattern) (ha : d127850 p = 1) (hb : d163361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127845 q = 1) (hb : d163356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127845, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127845, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33656 q ha hb
  have h2 (q : Pattern) (ha : d127846 q = 1) (hb : d163357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127846, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127846, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127847 q = 1) (hb : d163358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127847, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127847, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127848 q = 1) (hb : d163359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127848, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127848, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127849 q = 1) (hb : d163360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127849, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127849, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127850 q = 1) (hb : d163361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127850, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127850, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33658 (p : Pattern) (ha : d127976 p = 1) (hb : d162992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127957 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127891 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33537 q ha hb
    | true =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
  have h5 (q : Pattern) (ha : d127958 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127958, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127958, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127972 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d127973 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127973, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127973, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d127974 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127974, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127974, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127975 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127975, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127975, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127976 q = 1) (hb : d162992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127976, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127976, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33659 (p : Pattern) (ha : d127998 p = 1) (hb : d163002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127926 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127891 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33537 q ha hb
    | true =>
      simp only [d127891, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33538 q ha hb
  have h4 (q : Pattern) (ha : d127958 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127958, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d127958, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127972 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d127973 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127973, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127973, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127974 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127974, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127974, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127975 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127975, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127975, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127982 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127987 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127990 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d127901 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127901, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33540 q ha hb
    | true =>
      simp only [d127901, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33541 q ha hb
  have h13 (q : Pattern) (ha : d127991 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127991, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d127991, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127994 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127995 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127995, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127995, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127996 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127996, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d127996, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d127997 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127997, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127997, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d127998 q = 1) (hb : d163002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127998, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d127998, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33660 (p : Pattern) (ha : d128023 p = 1) (hb : d163368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127990 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127901 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127901, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33540 q ha hb
    | true =>
      simp only [d127901, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33541 q ha hb
  have h3 (q : Pattern) (ha : d127991 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127991, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127991, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127995 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127995, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127995, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128021 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128021, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128021, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128022 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128022, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128022, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128023 q = 1) (hb : d163368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128023, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128023, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33661 (p : Pattern) (ha : d128093 p = 1) (hb : d163160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128059 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33571 q ha hb
    | true =>
      simp only [d128059, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
  have h2 (q : Pattern) (ha : d128060 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128060, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128061 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128061, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128062 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128062, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h5 (q : Pattern) (ha : d128063 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128063, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128064 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128064, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128065 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128065, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128079 q = 1) (hb : d163145 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128079, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33572 q ha hb
    | true =>
      simp only [d128079, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22394 q hb ha
  have h9 (q : Pattern) (ha : d128080 q = 1) (hb : d163146 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128080, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128080, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128081 q = 1) (hb : d163147 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128081, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128081, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128082 q = 1) (hb : d163148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128082, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128082, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d163159 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128092, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128093 q = 1) (hb : d163160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128093, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128093, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro33662 (p : Pattern) (ha : d128099 p = 1) (hb : d163377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128094 q = 1) (hb : d163161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128094, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33661 q ha hb
    | true =>
      simp only [d128094, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128095 q = 1) (hb : d163162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128095, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128095, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128085 q = 1) (hb : d163151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128085, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33576 q ha hb
    | true =>
      simp only [d128085, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128086 q = 1) (hb : d163152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128086, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128086, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128096 q = 1) (hb : d163374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128096, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128096, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128097 q = 1) (hb : d163375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128097, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128097, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128098 q = 1) (hb : d163376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128098, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128098, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128099 q = 1) (hb : d163377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128099, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128099, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro33663 (p : Pattern) (ha : d128123 p = 1) (hb : d163383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128104 q = 1) (hb : d163378 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128104, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33662 q ha hb
    | true =>
      simp only [d128104, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33581 q ha hb
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d163379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128105, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128120 q = 1) (hb : d163380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128121 q = 1) (hb : d163381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128122 q = 1) (hb : d163382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128123 q = 1) (hb : d163383 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33664 (p : Pattern) (ha : d128136 p = 1) (hb : d163389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127999 q = 1) (hb : d163003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127999, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33658 q ha hb
    | true =>
      simp only [d127999, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33659 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128018 q = 1) (hb : d163004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128018, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128018, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128019 q = 1) (hb : d163366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128019, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128019, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128020 q = 1) (hb : d163367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128020, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128020, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128024 q = 1) (hb : d163369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128024, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128024, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33660 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128026 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128027 q = 1) (hb : d163370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128027, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128027, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128028 q = 1) (hb : d163371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128028, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128028, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d128029 q = 1) (hb : d163372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128029, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128029, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d128030 q = 1) (hb : d163373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128030, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128030, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128124 q = 1) (hb : d163384 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128124, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33663 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d128131 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128132 q = 1) (hb : d163385 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128132, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128133 q = 1) (hb : d163386 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128133, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d128134 q = 1) (hb : d163387 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128134, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d128135 q = 1) (hb : d163388 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128135, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d128136 q = 1) (hb : d163389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128136, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33665 (p : Pattern) (ha : d128142 p = 1) (hb : d163395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d163390 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33664 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d163391 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d163392 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d163393 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d163394 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d163395 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33666 (p : Pattern) (ha : d128148 p = 1) (hb : d163401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d163270 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33629 q ha hb
    | true =>
      simp only [d127103, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33635 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d163297 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33641 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d163298 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d163329 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33649 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d163330 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d163331 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d163362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33657 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d163363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d163364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d163365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d163396 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33665 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d163397 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d163398 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d163399 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d163400 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d163401 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro33667 (p : Pattern) (ha : d128154 p = 1) (hb : d163407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d163402 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33666 q ha hb
    | true =>
      simp only [d128149, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d163403 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d163404 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d163405 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d163406 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d163407 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33668 (p : Pattern) (ha : d128160 p = 1) (hb : d163413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d163408 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33667 q ha hb
    | true =>
      simp only [d128155, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d163409 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d163410 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d163411 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d163412 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d163413 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33669 (p : Pattern) (ha : d128166 p = 1) (hb : d163419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d163414 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33668 q ha hb
    | true =>
      simp only [d128161, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d163415 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d163416 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d163417 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d163418 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d163419 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33670 (p : Pattern) (ha : d128172 p = 1) (hb : d163425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d163420 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33669 q ha hb
    | true =>
      simp only [d128167, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d163421 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d163422 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d163423 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d163424 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d163425 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33671 (p : Pattern) (ha : d128178 p = 1) (hb : d163431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d163426 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33670 q ha hb
    | true =>
      simp only [d128173, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d163427 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d163428 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d163429 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d163430 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d163431 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33672 (p : Pattern) (ha : d128184 p = 1) (hb : d163437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d163432 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33671 q ha hb
    | true =>
      simp only [d128179, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d163433 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d163434 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d163435 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d163436 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d163437 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33673 (p : Pattern) (ha : d128190 p = 1) (hb : d163443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d163438 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33672 q ha hb
    | true =>
      simp only [d128185, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d163439 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d163440 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d163441 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d163442 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d163443 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33674 (p : Pattern) (ha : d12289 p = 1) (hb : d128195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12234 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12285 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12285, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12286 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12286, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12287 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12287, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12288 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12288, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12289 q = 1) (hb : d128195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33675 (p : Pattern) (ha : d12296 p = 1) (hb : d128200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12234 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12285 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12285, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12286 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12286, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12287 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12287, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12288 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d12241 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12292 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12292, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12293 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12293, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12294 q = 1) (hb : d128198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12294, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12295 q = 1) (hb : d128199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12295, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12296 q = 1) (hb : d128200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12296, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33676 (p : Pattern) (ha : d128207 p = 1) (hb : d150329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12241 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12292, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12293 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12294 q = 1) (hb : d128205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12295 q = 1) (hb : d128206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d150329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro33677 (p : Pattern) (ha : d128217 p = 1) (hb : d150339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12268 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128213 q = 1) (hb : d150335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d150336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128214, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d150337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d150338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d150339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33678 (p : Pattern) (ha : d128223 p = 1) (hb : d150345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d128201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33674 q ha hb
    | true =>
      simp only [d12297, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33675 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12298 q = 1) (hb : d128202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128203 q = 1) (hb : d150327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128203, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128204 q = 1) (hb : d150328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128204, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128208 q = 1) (hb : d150330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128208, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33676 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128209 q = 1) (hb : d150331 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128209, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128210 q = 1) (hb : d150332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128210, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128211 q = 1) (hb : d150333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128211, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128212 q = 1) (hb : d150334 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128212, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128218 q = 1) (hb : d150340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128218, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33677 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128219 q = 1) (hb : d150341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128219, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128220 q = 1) (hb : d150342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128220, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128221 q = 1) (hb : d150343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128221, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128222 q = 1) (hb : d150344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128222, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128223 q = 1) (hb : d150345 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128223, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33679 (p : Pattern) (ha : d128229 p = 1) (hb : d150351 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d150346 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33678 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d150347 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d150348 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d150349 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d150350 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d150351 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro33680 (p : Pattern) (ha : d128234 p = 1) (hb : d162176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128230 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128230, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128231 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128231, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d128232 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128232, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128233 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128233, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128234 q = 1) (hb : d162176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33681 (p : Pattern) (ha : d128239 p = 1) (hb : d162185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128230 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128230, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d128231 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128231, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128232 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128232, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128233 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128233, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d128235 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d128235, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128236 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128236, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128237 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128237, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128238 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128238, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128239 q = 1) (hb : d162185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128239, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33682 (p : Pattern) (ha : d128246 p = 1) (hb : d163246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128235 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128235, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128236, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d163246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33683 (p : Pattern) (ha : d128256 p = 1) (hb : d163257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163252 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128252 q = 1) (hb : d163253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128252, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d163254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128253, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d163255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d163256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d163257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33684 (p : Pattern) (ha : d128262 p = 1) (hb : d163263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128240 q = 1) (hb : d162186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33680 q ha hb
    | true =>
      simp only [d128240, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33681 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128241 q = 1) (hb : d162187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128241, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128242 q = 1) (hb : d163244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128242, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128243 q = 1) (hb : d163245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128243, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128247 q = 1) (hb : d163247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128247, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33682 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128248 q = 1) (hb : d163248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128248, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128249 q = 1) (hb : d163249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128249, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128250 q = 1) (hb : d163250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128250, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128251 q = 1) (hb : d163251 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128251, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128257 q = 1) (hb : d163258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128257, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33683 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128258 q = 1) (hb : d163259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128258, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128259 q = 1) (hb : d163260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128259, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128260 q = 1) (hb : d163261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128260, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128261 q = 1) (hb : d163262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128261, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128262 q = 1) (hb : d163263 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128262, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33685 (p : Pattern) (ha : d128268 p = 1) (hb : d163269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d163264 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33684 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d163265 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d163266 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d163267 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d163268 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d163269 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33686 (p : Pattern) (ha : d128274 p = 1) (hb : d162327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128270 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128270, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128271 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128271, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d128272 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128272, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128273 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128273, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128274 q = 1) (hb : d162327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33687 (p : Pattern) (ha : d128279 p = 1) (hb : d162336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128270 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128270, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d128271 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128271, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128272 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128272, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128273 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128273, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16325 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d128275 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d128275, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128276 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128276, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128277 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128277, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128278 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128278, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128279 q = 1) (hb : d162336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128279, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33688 (p : Pattern) (ha : d128286 p = 1) (hb : d163273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128275 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128275, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128276, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d163273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33689 (p : Pattern) (ha : d128296 p = 1) (hb : d163284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163279 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128292 q = 1) (hb : d163280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128292, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16419 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d163281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128293, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d163282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d163283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d163284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33690 (p : Pattern) (ha : d128302 p = 1) (hb : d163290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128280 q = 1) (hb : d162337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33686 q ha hb
    | true =>
      simp only [d128280, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33687 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128281 q = 1) (hb : d162338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128281, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128282 q = 1) (hb : d163271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128282, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128283 q = 1) (hb : d163272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128283, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128287 q = 1) (hb : d163274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128287, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33688 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128288 q = 1) (hb : d163275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128288, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128289 q = 1) (hb : d163276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128289, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128290 q = 1) (hb : d163277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128290, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128291 q = 1) (hb : d163278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128291, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128297 q = 1) (hb : d163285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128297, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33689 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128298 q = 1) (hb : d163286 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128298, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128299 q = 1) (hb : d163287 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128299, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128300 q = 1) (hb : d163288 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128300, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128301 q = 1) (hb : d163289 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128301, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128302 q = 1) (hb : d163290 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128302, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33691 (p : Pattern) (ha : d128308 p = 1) (hb : d163296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d163291 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33690 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d163292 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d163293 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d163294 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d163295 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d163296 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33692 (p : Pattern) (ha : d128315 p = 1) (hb : d162502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128311 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128311, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128312 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128312, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d128313 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128313, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128314 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128314, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128315 q = 1) (hb : d162502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128315, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33693 (p : Pattern) (ha : d128320 p = 1) (hb : d162512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128311 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128311, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d128312 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128312, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128313 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128313, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128314 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128314, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d128316 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d128316, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128317 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128317, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128318 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128318, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128319 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128319, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128320 q = 1) (hb : d162512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128320, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33694 (p : Pattern) (ha : d128327 p = 1) (hb : d163301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128316 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128316, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128317 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128317, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128325 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128326 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d163301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33695 (p : Pattern) (ha : d128337 p = 1) (hb : d163316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128333 q = 1) (hb : d163312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128333, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d163313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128334, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d163314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d163315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d163316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33696 (p : Pattern) (ha : d128343 p = 1) (hb : d163322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16489 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128321 q = 1) (hb : d162513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33692 q ha hb
    | true =>
      simp only [d128321, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33693 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128322 q = 1) (hb : d162514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128322, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128323 q = 1) (hb : d163299 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128323, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128324 q = 1) (hb : d163300 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128324, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128328 q = 1) (hb : d163302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128328, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33694 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128329 q = 1) (hb : d163303 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128329, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128330 q = 1) (hb : d163304 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128330, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128331 q = 1) (hb : d163305 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128331, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128332 q = 1) (hb : d163306 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128332, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128338 q = 1) (hb : d163317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128338, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33695 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16772 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128339 q = 1) (hb : d163318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128339, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128340 q = 1) (hb : d163319 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128340, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128341 q = 1) (hb : d163320 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128341, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128342 q = 1) (hb : d163321 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128342, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128343 q = 1) (hb : d163322 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128343, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33697 (p : Pattern) (ha : d128349 p = 1) (hb : d163328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d163323 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33696 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d163324 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d163325 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d163326 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d163327 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d163328 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33698 (p : Pattern) (ha : d128357 p = 1) (hb : d162748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128353 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128353, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16942 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128354 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128354, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d128355 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128355, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128356 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128356, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128357 q = 1) (hb : d162748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128357, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128357, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33699 (p : Pattern) (ha : d128362 p = 1) (hb : d162758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16849 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16858 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16890 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128353 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128353, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16942 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d128354 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128354, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128355 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128355, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128356 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128356, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16957 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16960 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d128358 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d128358, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128359 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128359, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128360 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128360, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128360, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128361 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128361, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128361, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128362 q = 1) (hb : d162758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128362, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128362, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33700 (p : Pattern) (ha : d128369 p = 1) (hb : d163334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128358 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128358, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128359 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128359, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128367 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128368 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d163334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33701 (p : Pattern) (ha : d128379 p = 1) (hb : d163349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128375 q = 1) (hb : d163345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128375, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17121 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d163346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128376, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d163347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d163348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d163349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33702 (p : Pattern) (ha : d128385 p = 1) (hb : d163355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128363 q = 1) (hb : d162759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128363, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33698 q ha hb
    | true =>
      simp only [d128363, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33699 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16990 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128364 q = 1) (hb : d162760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128364, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128364, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128365 q = 1) (hb : d163332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128365, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128366 q = 1) (hb : d163333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128366, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128370 q = 1) (hb : d163335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128370, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33700 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16999 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128371 q = 1) (hb : d163336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128371, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128372 q = 1) (hb : d163337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128372, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128373 q = 1) (hb : d163338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128373, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128374 q = 1) (hb : d163339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128374, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128380 q = 1) (hb : d163350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128380, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33701 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128381 q = 1) (hb : d163351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128381, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128382 q = 1) (hb : d163352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128382, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128383 q = 1) (hb : d163353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128383, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128384 q = 1) (hb : d163354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128384, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128385 q = 1) (hb : d163355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128385, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33703 (p : Pattern) (ha : d128391 p = 1) (hb : d163361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d163356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33702 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d163357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d163358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d163359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d163360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d163361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33704 (p : Pattern) (ha : d128400 p = 1) (hb : d162992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17215 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17224 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17255 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128396 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128396, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17307 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128397 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128397, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d128398 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128398, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128399 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128399, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128400 q = 1) (hb : d162992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128400, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128400, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33705 (p : Pattern) (ha : d128405 p = 1) (hb : d163002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128396 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128396, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17307 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d128397 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128397, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128398 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128398, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128399 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128399, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17317 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d17322 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d17325 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d128401 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d128401, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128402 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128402, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128403 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128403, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128403, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128404 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128404, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128404, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128405 q = 1) (hb : d163002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128405, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128405, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33706 (p : Pattern) (ha : d128412 p = 1) (hb : d163368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128401 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128401, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128402 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128402, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128410 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128411 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d163368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33707 (p : Pattern) (ha : d128422 p = 1) (hb : d163383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163378 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128418 q = 1) (hb : d163379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128418, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17485 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d163380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128419, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d163381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d163382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d163383 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33708 (p : Pattern) (ha : d128428 p = 1) (hb : d163389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17207 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128406 q = 1) (hb : d163003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128406, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33704 q ha hb
    | true =>
      simp only [d128406, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33705 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128407 q = 1) (hb : d163004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128407, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128407, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128408 q = 1) (hb : d163366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128408, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128409 q = 1) (hb : d163367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128409, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128413 q = 1) (hb : d163369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128413, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33706 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d17364 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128414 q = 1) (hb : d163370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128414, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128415 q = 1) (hb : d163371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128415, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128416 q = 1) (hb : d163372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128416, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128417 q = 1) (hb : d163373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128417, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128423 q = 1) (hb : d163384 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128423, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33707 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17501 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128424 q = 1) (hb : d163385 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128424, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128425 q = 1) (hb : d163386 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128425, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128426 q = 1) (hb : d163387 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128426, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128427 q = 1) (hb : d163388 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128427, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128428 q = 1) (hb : d163389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128428, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33709 (p : Pattern) (ha : d128434 p = 1) (hb : d163395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d163390 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33708 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d163391 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d163392 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d163393 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d163394 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d163395 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33710 (p : Pattern) (ha : d128440 p = 1) (hb : d163401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d163270 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33679 q ha hb
    | true =>
      simp only [d128269, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33685 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d163297 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33691 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d163298 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d163329 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33697 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d163330 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d163331 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d163362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33703 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d163363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d163364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d163365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d163396 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33709 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d163397 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d163398 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d163399 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d163400 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d163401 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro33711 (p : Pattern) (ha : d128446 p = 1) (hb : d163407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d163402 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33710 q ha hb
    | true =>
      simp only [d128441, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d163403 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d163404 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d163405 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d163406 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d163407 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33712 (p : Pattern) (ha : d128452 p = 1) (hb : d163413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d163408 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33711 q ha hb
    | true =>
      simp only [d128447, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d163409 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d163410 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d163411 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d163412 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d163413 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33713 (p : Pattern) (ha : d128458 p = 1) (hb : d163419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d163414 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33712 q ha hb
    | true =>
      simp only [d128453, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d163415 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d163416 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d163417 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d163418 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d163419 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33714 (p : Pattern) (ha : d128464 p = 1) (hb : d163425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d163420 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33713 q ha hb
    | true =>
      simp only [d128459, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d163421 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d163422 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d163423 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d163424 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d163425 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33715 (p : Pattern) (ha : d128470 p = 1) (hb : d163431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d163426 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33714 q ha hb
    | true =>
      simp only [d128465, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d163427 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d163428 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d163429 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d163430 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d163431 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33716 (p : Pattern) (ha : d128476 p = 1) (hb : d163437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d163432 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33715 q ha hb
    | true =>
      simp only [d128471, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d163433 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d163434 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d163435 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d163436 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d163437 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33717 (p : Pattern) (ha : d128482 p = 1) (hb : d163443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d163438 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33716 q ha hb
    | true =>
      simp only [d128477, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d163439 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d163440 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d163441 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d163442 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d163443 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33718 (p : Pattern) (ha : d125742 p = 1) (hb : d163444 p = 1) : d125742 p = 1 := by
  have h0 (q : Pattern) (ha : d125742 q = 1) (hb : d163444 q = 1) : d125742 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro33719 (p : Pattern) (ha : d13981 p = 1) (hb : d51995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13980 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13980, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13981 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13981, d51995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13981, d51995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro33720 (p : Pattern) (ha : d13987 p = 1) (hb : d52001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13982 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33719 q ha hb
    | true =>
      simp only [d13982, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d13983 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13984 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13985 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13985, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13986 q = 1) (hb : d52000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13986, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13987 q = 1) (hb : d52001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13987, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro33721 (p : Pattern) (ha : d13993 p = 1) (hb : d52007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13993 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13993, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33722 (p : Pattern) (ha : d52013 p = 1) (hb : d125417 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d125413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
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
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d125414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d125415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d125416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52013 q = 1) (hb : d125417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro33723 (p : Pattern) (ha : d14000 p = 1) (hb : d52023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14000 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14000, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33724 (p : Pattern) (ha : d52029 p = 1) (hb : d125422 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d125413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
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
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d125414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d125415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d125416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d14001 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
    | true =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52025 q = 1) (hb : d125418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52025, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d52026 q = 1) (hb : d125419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d52026, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d52027 q = 1) (hb : d125420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52027, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d52028 q = 1) (hb : d125421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d52028, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d52029 q = 1) (hb : d125422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52029, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro33725 (p : Pattern) (ha : d52038 p = 1) (hb : d125429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
    | true =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52025 q = 1) (hb : d125418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52025, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52026 q = 1) (hb : d125419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52026, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52036 q = 1) (hb : d125427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52037 q = 1) (hb : d125428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52038 q = 1) (hb : d125429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33726 (p : Pattern) (ha : d14020 p = 1) (hb : d52049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14019 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14019, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h10 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14020 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14020, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14020, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro33727 (p : Pattern) (ha : d14026 p = 1) (hb : d52055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14021 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33726 q ha hb
    | true =>
      simp only [d14021, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d14022 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14023 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14024 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14024, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14025 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14025, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14026 q = 1) (hb : d52055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14026, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro33728 (p : Pattern) (ha : d14032 p = 1) (hb : d52061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33727 q ha hb
    | true =>
      simp only [d14027, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14029 q = 1) (hb : d52058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14029, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14030 q = 1) (hb : d52059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14030, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14031 q = 1) (hb : d52060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14031, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14032 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14032, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33729 (p : Pattern) (ha : d52067 p = 1) (hb : d125439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33728 q ha hb
    | true =>
      simp only [d14033, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d125435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52063, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d125436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d125437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d125438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d125439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33730 (p : Pattern) (ha : d52073 p = 1) (hb : d125445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52030 q = 1) (hb : d125423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33722 q ha hb
    | true =>
      simp only [d52030, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33724 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d125424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52033, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d125425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d125426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52039 q = 1) (hb : d125430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52039, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33725 q ha hb
  have h12 (q : Pattern) (ha : d52040 q = 1) (hb : d125431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52040, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52041 q = 1) (hb : d125432 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52041, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52042 q = 1) (hb : d125433 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52042, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d125434 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52068 q = 1) (hb : d125440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52068, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33729 q ha hb
  have h17 (q : Pattern) (ha : d52069 q = 1) (hb : d125441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52069, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52070 q = 1) (hb : d125442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52070, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52071 q = 1) (hb : d125443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52071, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52072 q = 1) (hb : d125444 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d52072, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d125445 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro33731 (p : Pattern) (ha : d14054 p = 1) (hb : d52083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14054 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33732 (p : Pattern) (ha : d14061 p = 1) (hb : d52090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14001 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
    | true =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d14057 q = 1) (hb : d52086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14058 q = 1) (hb : d52087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14058, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14059 q = 1) (hb : d52088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14060 q = 1) (hb : d52089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14061 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14061, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33733 (p : Pattern) (ha : d14141 p = 1) (hb : d52163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14141 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14141, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33734 (p : Pattern) (ha : d14066 p = 1) (hb : d52095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14066 q = 1) (hb : d52095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14066, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33735 (p : Pattern) (ha : d14073 p = 1) (hb : d52102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14073 q = 1) (hb : d52102 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14073, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33736 (p : Pattern) (ha : d14079 p = 1) (hb : d126874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14077 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14077, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14078 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14078, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14079 q = 1) (hb : d126874 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14079, d126874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14079, d126874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro33737 (p : Pattern) (ha : d14085 p = 1) (hb : d126880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d126875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33736 q ha hb
    | true =>
      simp only [d14080, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33719 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d126876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d126876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d126876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d126877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d126877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d126877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13982 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33719 q ha hb
    | true =>
      simp only [d13982, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d13983 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13984 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14083 q = 1) (hb : d126878 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d126878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, d126878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13985 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13985, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14084 q = 1) (hb : d126879 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, d126879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14084, d126879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14085 q = 1) (hb : d126880 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, d126880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14085, d126880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro33738 (p : Pattern) (ha : d14091 p = 1) (hb : d126886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d126881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33737 q ha hb
    | true =>
      simp only [d14086, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d126882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d126883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d126884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d126885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14091 q = 1) (hb : d126886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, d126886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14091, d126886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33739 (p : Pattern) (ha : d14112 p = 1) (hb : d68835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14112 q = 1) (hb : d68835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14112, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33740 (p : Pattern) (ha : d125455 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33734 q ha hb
    | true =>
      simp only [d14067, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33735 q ha hb
    | true =>
      simp only [d14074, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33738 q ha hb
    | true =>
      simp only [d14092, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d125451 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125451, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14113 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33739 q ha hb
    | true =>
      simp only [d14113, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14114 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14114, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d125452 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125452, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125453 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125453, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125454 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125454, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125455 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125455, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro33741 (p : Pattern) (ha : d14119 p = 1) (hb : d52144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14119 q = 1) (hb : d52144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14119, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33742 (p : Pattern) (ha : d14124 p = 1) (hb : d52149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14124 q = 1) (hb : d52149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14124, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14124, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33743 (p : Pattern) (ha : d14128 p = 1) (hb : d126893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d126881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33737 q ha hb
    | true =>
      simp only [d14086, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d126882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d126883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d126884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d126885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14128 q = 1) (hb : d126893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14128, d126893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14128, d126893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33744 (p : Pattern) (ha : d14133 p = 1) (hb : d74081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33720 q ha hb
    | true =>
      simp only [d13988, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14133 q = 1) (hb : d74081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14133, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14133, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33745 (p : Pattern) (ha : d125460 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33734 q ha hb
    | true =>
      simp only [d14067, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33735 q ha hb
    | true =>
      simp only [d14074, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33738 q ha hb
    | true =>
      simp only [d14092, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d125451 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125451, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14113 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33739 q ha hb
    | true =>
      simp only [d14113, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14114 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14114, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d125452 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125452, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125453 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125453, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125454 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125454, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14120 q = 1) (hb : d52145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14120, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33741 q ha hb
    | true =>
      simp only [d14120, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d14121 q = 1) (hb : d52146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14121, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14121, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14122 q = 1) (hb : d52147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14122, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d14122, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d14123 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14123, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14123, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14125 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14125, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33742 q ha hb
    | true =>
      simp only [d14125, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d14126 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14126, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14126, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d14127 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14127, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d14127, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d14129 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33743 q ha hb
    | true =>
      simp only [d14129, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d125456 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125456, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d14134 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33744 q ha hb
    | true =>
      simp only [d14134, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d14135 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d14135, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d125457 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d125457, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125458 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125458, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d125459 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125459, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d125460 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125460, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro33746 (p : Pattern) (ha : d125467 p = 1) (hb : d126906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14129 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33743 q ha hb
    | true =>
      simp only [d14129, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125456 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125456, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14134 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33744 q ha hb
    | true =>
      simp only [d14134, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14135 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14135, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125457 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125457, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125465 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125465, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125466 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125466, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125467 q = 1) (hb : d126906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, d126906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125467, d126906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro33747 (p : Pattern) (ha : d14156 p = 1) (hb : d126912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14154 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14154, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12600 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12601 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12602 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d14155 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14155, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14156 q = 1) (hb : d126912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14156, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14156, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro33748 (p : Pattern) (ha : d14162 p = 1) (hb : d126918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14157 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33747 q ha hb
    | true =>
      simp only [d14157, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33726 q ha hb
  have h2 (q : Pattern) (ha : d14158 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14159 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14021 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33726 q ha hb
    | true =>
      simp only [d14021, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d14022 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14023 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14160 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14160, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14024 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14024, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14161 q = 1) (hb : d126917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14161, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14161, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14162 q = 1) (hb : d126918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14162, d126918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14162, d126918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro33749 (p : Pattern) (ha : d14168 p = 1) (hb : d126924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14163 q = 1) (hb : d126919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14163, d126919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33748 q ha hb
    | true =>
      simp only [d14163, d126919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14164 q = 1) (hb : d126920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14164, d126920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14164, d126920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14027 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33727 q ha hb
    | true =>
      simp only [d14027, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14028 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14165 q = 1) (hb : d126921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14165, d126921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14165, d126921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14166 q = 1) (hb : d126922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14166, d126922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14166, d126922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14167 q = 1) (hb : d126923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14167, d126923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14167, d126923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14168 q = 1) (hb : d126924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14168, d126924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14168, d126924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
